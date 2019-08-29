library(MASS)
library(Matrix)
library(mvtnorm)
library(grpreg)
library(splines)
library(plyr)

## standardize each column of X
standardize = function(X){
  N = nrow(X)
  center = colMeans(X)
  X = sweep(X,2,center)
  scale = sqrt(apply(X,2,crossprod)/N)
  val = sweep(X,2,scale,"/")
  attr(val,"center") = center
  attr(val,"scale") = scale
  return(val)
}
## orthogonalize each groups of X
orthogonalize = function(X,group){
  if (ncol(X)!=length(group)) stop("ncols of X is not equal to length of group.")
  N = nrow(X)
  G = max(group)
  Tr = vector("list",G)
  if (!identical(as.integer(unique(group)),as.integer(1:G)))
    stop("Groups must be consecutively numbered 1,2,3,...")
  X_orth = matrix(0,nrow=nrow(X),ncol=ncol(X))
  for (g in seq(G)){
    ind = which(group==g)
    SVD = svd(crossprod(X[,ind,drop=FALSE])/N)
    r = which(SVD$d>1e-10)   ## in case of nearly completely collinearity within a group
    Tr[[g]] = sweep(SVD$u[,r,drop=FALSE],2,SVD$d[r]^(-1/2),"*")
    X_orth[,ind[r]] = X[,ind]%*%Tr[[g]]
  }
  nz = !apply(X_orth==0,2,all)
  X_orth = X_orth[,nz,drop=FALSE]
  attr(X_orth,"Tr") = Tr
  attr(X_orth,"group") = group[nz]
  return(X_orth)
}

## Generate nonparametric functions
genr.np.func <- function(U){
  n <- nrow(U)
  q <- ncol(U)
  f <- vector(mode = "list", 2)
  f[[1]] <- function(x)  sin(4 * pi * x)       # integrate(f,-3,3)=0
  f[[2]] <- function(x)  10*(exp(-3.25*x) + 4*exp(-6.5*x) + 3*exp(-9.75*x))
  fU <- matrix(0, n, q)
  for (i in 1:q)
  {
    if (i%%2 == 1) fU[, i] <- f[[1]](U[, i])
    else fU[, i] <- f[[2]](U[, i])
  }
  return(fU)
}

#input index of interaction and output main effects
my.index <- function(num, p){
  a <- (p - 1):1
  a <- cumsum(a)
  a <- c(0, a)
  for(j in 1:(p - 1))
  {
    if(num > a[j] & num <= a[j + 1])
    {
      r1 <- j
      r2 <- num - a[j] + j
    }
  }
  result <- c(r1, r2)
  return(result)
}

## get interactions of X and X or X and fU
get.interac <- function(X, fU = NULL){
  p <- ncol(X)
  if (is.null(fU))
  {
    IXX <- NULL
    for (k in 1:(p - 1)) IXX <- cbind(IXX, X[, (k + 1):p] * X[, k])
    return(IXX)
  }
  else
  {
    if (nrow(fU) != nrow(X)) stop("nrows of fU is not equal to nrows of X.")
    q <- ncol(fU)
    IXU <- NULL
    for (k in 1:q) IXU <- cbind(IXU, X * fU[, k])
    return(IXU)
  }
}

## Change n*p X into n*3p X with 0 in column
changeNotes <- function(x, n, totaln, m, p){
  ind <- m * seq(0, p - 1)
  ind3 <- cumsum(n)
  ind2 <- c(0, ind3[-length(ind3)]) + 1
  xx <- c()
  if(m > 1){
    for(i in 1:m){
      xx0 <- matrix(0, n[i], m * p)
      xx0[, i + ind] <- x[(ind2[i]:ind3[i]), ]
      xx <- rbind(xx, xx0)
    }
  } else xx <- x
  return(xx)
}

##### get the subscript of the interaction
#if m>1, output three continous indexs in three datasets(long vector)
index.interac <- function(index.main, p, m){
  if (!all(index.main %in% 1:p)) stop("elements of index.main is wrong.")
  index.main <- sort(index.main)
  low <- as.vector(lower.tri(matrix(0, p, p)))
  low[low] <- 1:(p * (p - 1) / 2)
  Matr <- matrix(low, p, p, byrow = T)
  index.int <- as.vector(t(Matr[index.main, index.main]))
  index.int <- index.int[index.int != 0]
  index.int <- ((index.int - 1) * m + 1) : (index.int * m) 
  return(index.int)
}

## get p-th dataset
data.regener <- function(data, n, p){
  Y <- data$Y; X <- data$X;  U <- data$U; fU <- data$fU;  IX <- data$IX;
  n <- cumsum(c(0, n))
  newdata <- list(Y = Y[(n[p] + 1):n[p + 1]], XX = X[(n[p] + 1):n[p + 1], ], 
                  IXX = IX[(n[p] + 1):n[p + 1], ], U = U[(n[p] + 1):n[p + 1], ], 
                  fU = fU[(n[p] + 1):n[p + 1], ])
  return(newdata)
}

## get alpha (interactions of beta) from beta (and gamma) #use in reparametrization
beta.to.alpha2 <- function(beta, gamma = NULL){
  p <- length(beta)
  Ibeta <- NULL
  for (k in 1:(p - 1)) Ibeta <- c(Ibeta, beta[k] * beta[(k + 1):p])
  if (is.null(gamma)) alpha <- Ibeta
  else
  {
    if (length(gamma) != p * (p - 1) / 2) stop("length of gamma and beta must match.")
    else alpha <- Ibeta*gamma
  }
  return(alpha)
}
beta.to.alpha <- function(beta, m, gamma = NULL){
  beta <- matrix(beta, ncol = m, byrow = T)
  Ibeta <- NULL
  for (i in 1:ncol(beta)) Ibeta = c(Ibeta, beta.to.alpha2(beta[, i])) #There gamma is NULL 
  Ibeta <- matrix(Ibeta, nrow = m, byrow = T)
  Ibeta <- as.vector(Ibeta)
  if (is.null(gamma)) alpha <- Ibeta
  else {alpha <- Ibeta * gamma}
  return(alpha)
}

## get nonparametric function from B-spline basis matrix B and coeffieients phi
get.np.func <- function(B, phi, q, df, n){
  mm <- length(n)
  if (ncol(B) != sum(df) | length(phi) != mm * sum(df)) stop("dimensions of B or phi are wrong.")
  totaln <- nrow(B); dfcum <- c(0,cumsum(df))
  nn <- cumsum(c(0, n))
  fU <- matrix(0, totaln, q)
  phi_new <- matrix(phi, nrow = mm, byrow = T)
  for(j in 1:mm){
    for (i in 1:q) {
      fU[(nn[j] + 1):nn[j + 1], i] <- B[(nn[j] + 1):nn[j + 1], (dfcum[i]+1):(dfcum[i+1])] %*% phi_new[j, (dfcum[i]+1):(dfcum[i+1])] 
    }
  }
  return(fU)
}

##### Generate the data for semiparametric interaction model with continuous response #####
data.gener <- function(n, p, q, beta.true, alpha.true){
  # n: number of subjects, it's a vector
  # p: number of covariables in parametric components X
  # q: number of covariables in nonparametric components U
  # beta.true: the coefficients of X: p-dimensional
  # alpha.true: the coefficients of interactions of X: p*(p-1)/2-dimensional
  # m: number of datasets
  # totaln: number of total subjects
  m <- length(n); totaln <- sum(n); nn <- cumsum(c(0, n))
  X <- matrix(0, totaln, p); U <- matrix(0, totaln, q); err <- rep(0, totaln)
  X <- rmvnorm(totaln, mean = rep(0, p), sigma = diag(p)) #covariates are independent
  U <- matrix(runif(totaln * q, min = 0, max = 1), nr = totaln)   
  err <- rnorm(totaln, mean = 0, sd = 1)
  fU <- genr.np.func(U[, 1:q, drop = FALSE]); fU <- standardize(fU)   # nonparametric function of U
  IX <- get.interac(X)          # interactions of X and X
  IXX <- changeNotes(IX, n, totaln, m, p*(p-1)/2)
  # XX: changed X
  # X: original X
  XX <- changeNotes(X, n, totaln, m, p)
  Y <- drop(XX %*% beta.true + rowSums(fU) + IXX %*% alpha.true + err)
  data <- list(Y = Y, X = X, XX = XX, IX = IX, IXX = IXX, U = U, fU = fU)
  return(list(data = data, Y = Y, X = X, XX = XX, U = U, IX = IX, IXX = IXX, fU = fU, n = n,
              p = p, q = q, beta.true = beta.true, alpha.true = alpha.true))
}

#######################################################
## algorithm ##
est.block <- function(n, Y, X, XX, U, IXX, fU, p, df_bs = Nbs, eps1 = .001){
  # B-spline, df_bs is number of the B-spline basis function
  totaln <- length(Y); m <- length(n); q <- ncol(U); pp <- p * m
  B <- B1 <- matrix(0, totaln, sum(df_bs))   
  nn <- cumsum(c(0, n))
  Dcum = c(0,cumsum(df_bs))
  for(j in 1:m){
    for (i in 1:q) {
      B1[(nn[j] + 1):nn[j + 1],(Dcum[i]+1):(Dcum[i+1])] = as.matrix(bs(U[(nn[j] + 1):nn[j + 1],i],df=df_bs[i]))
    }
    B[(nn[j] + 1):nn[j + 1], ] = standardize(B1[(nn[j] + 1):nn[j + 1], ])
    B[(nn[j] + 1):nn[j + 1], ] = orthogonalize(B[(nn[j] + 1):nn[j + 1], ],rep(1:q,times=df_bs))
  }
  Y <- Y - mean(Y);  X <- standardize(X); IXX <- standardize(IXX); XX <- standardize(XX); fU <- standardize(fU)
  XB <- cbind(X, IXX, B) 
  #ridge regression as initial estimates
  sol <- lm.ridge(Y ~ XB, lambda = seq(0, 1, 0.01))
  ini_ols <- as.vector(sol$coef[, which.min(sol$GCV)])
  phi_o <- ini_ols[-(1:(m * (p + p * (p - 1) / 2)))]   # coefficients of the B-spline basis matrix: B
  phi_old <- rep(phi_o, 3)
  fU_old <- get.np.func(B, phi_old, q, df_bs, n)
  XB <- cbind(X, IXX) 
  YB <- Y - rowSums(fU_old)
  sol <- lm.ridge(YB ~ XB, lambda = seq(0, 1, 0.01))
  ini_ols <- as.vector(sol$coef[, which.min(sol$GCV)])
  beta_old <- ini_ols[1:pp]
  gamma_old <- ini_ols[(pp + 1):(m * (p + p * (p - 1) / 2))] / beta.to.alpha(beta_old, m)
  t <- 1      # t indexes the inner iterations
  repeat
  {
    ## update phi (or fU) from beta,  gamma 
    alpha_old <- beta.to.alpha(beta_old, m, gamma_old)    
    Y_tilde_hat <- Y - X %*% beta_old - IXX %*% alpha_old 
    XXU_tilde_hat <- B
    phi_new <- phi_old 
    for(ti in 1:m){
      Y_tilde <- Y_tilde_hat[(nn[ti] + 1):nn[ti + 1]]
      XXU_tilde <- XXU_tilde_hat[(nn[ti] + 1):nn[ti + 1],]
      if(ncol(B) >= nrow(B)){
        sol <- lm.ridge(Y_tilde ~ XXU_tilde, lambda = seq(0, 0.1, 0.0001))
        phi_new[((ti - 1)*sum(df_bs) + 1):(ti*sum(df_bs))] <- as.vector(sol$coef[, which.min(sol$GCV)])
      } else {
        sol <- lm(Y_tilde~XXU_tilde-1)
        phi_new[((ti - 1)*sum(df_bs) + 1):(ti*sum(df_bs))] <- sol$coef
      }
    }
    fU_new <- get.np.func(B, phi_new, q, df_bs, n)
    
    # update gamma and eta from beta and phi
    Y_tilde <- Y - X %*% beta_old - rowSums(fU_new) 
    Ibeta <- beta.to.alpha(beta_old, m)
    XX_tilde <- IXX %*% diag(Ibeta) 
    index <- 1 - apply(XX_tilde, 2, function(x) all(x == 0))
    ind <- matrix(index, ncol = m, byrow = T)
    ind[apply(ind, 1, sum)!=0, ] <- rep(1, m)
    index <- as.vector(t(ind))
    if (any(index == 0)){
      if (all(index == 0)) {
        gamma_new <- gamma_old
      } else {
        index0 <- which(index == 0)
        XX_tilde <- as.matrix(XX_tilde[, -index0])
        gamma_new <- rep(0, length(gamma_old))
        pq <- ncol(XX_tilde) / m
        groups <- NULL
        for(i in 1:pq){
          groups <- c(groups, rep(i, m))
        }
        alasso_res <- grpreg(XX_tilde, Y_tilde, group = groups, penalty = "grLasso", family = "gaussian",
                             lambda.min = 1e-1, nlambda = 100)
        gamma_new[-index0] <- drop(select(alasso_res, criterion = "BIC")$beta)[-1]
        lambda_gamma <- drop(select(alasso_res, criterion = "BIC")$lambda)
      }
    } else { 
      groups <- NULL
      for(i in 1:(p * (p - 1) / 2)){
        groups <- c(groups, rep(i, m))
      }
      alasso_res <- grpreg(XX_tilde, Y_tilde, group = groups, penalty = "grLasso", family = "gaussian",
                           lambda.min = 1e-1, nlambda = 100)
      gamma_new <- drop(select(alasso_res, criterion = "BIC")$beta)[-1]
      lambda_gamma <- drop(select(alasso_res, criterion="BIC")$lambda)
    }
    
    ## update beta from gamma,  phi (or fU) and eta
    beta_new <- beta_old
    alpha_new <- beta.to.alpha(beta_old, m, gamma_new)
    Y_tilde <- Y - IXX %*% alpha_new - rowSums(fU_new) 
    XXU_tilde <- X
    groups <- NULL
    for(i in 1:p){
      groups <- c(groups, rep(i, m))
    }
    block_res <- grpreg(XXU_tilde, Y_tilde, group = groups, penalty = "grLasso", family = "gaussian",
                        lambda.min = 1e-1, nlambda = 100)
    beta_new <- drop(select(block_res, criterion = "BIC")$beta)[-1]
    lambda_beta <- drop(select(block_res, criterion = "BIC")$lambda)
    
    if ((crossprod(beta_new - beta_old) <= eps1 &
         crossprod(gamma_new - gamma_old) <= eps1) | t > 50)
      break
    t <- t + 1
    beta_old <- beta_new
    gamma_old <- gamma_new
    phi_old <- phi_new
    fU_old <- fU_new
  }
  print(paste0("t=", t))
  beta3 <- matrix(beta_new, nrow = m, byrow = F)
  beta <- apply(beta3, 2, sum)
  beta3[, beta == 0] <- 0
  p1 <- sum(beta != 0)
  gamma3 <- matrix(gamma_new, nrow = m, byrow = F)
  gamma <- apply(gamma3, 2, sum)
  alpha <- beta.to.alpha(beta, 1, gamma) 
  p2 <- sum(alpha != 0)
  alpha3 <- matrix(0, ncol = ncol(gamma3), nrow = nrow(gamma3))
  X_final <-  standardize(XX[, beta != 0])
  IXX_final <- standardize(get.interac(XX)[, alpha != 0])
  X_reg <- cbind(X_final, IXX_final, B)
  XB_reg <- cbind(X_final, IXX_final)
  fU.est <- fU_old
  for(i in 1:m){
    YB <- Y[(nn[i] + 1):nn[i + 1]] - rowSums(fU.est[(nn[i] + 1):nn[i + 1], ])
    sol <- lm.ridge(YB ~ XB_reg[(nn[i] + 1):nn[i + 1], ], lambda = seq(0, 1, 0.01))
    ini_ols <- as.vector(sol$coef[, which.min(sol$GCV)])
    beta1 <- ini_ols[1:p1]
    alpha1 <- ini_ols[(p1 + 1):(p1 + p2)]
    beta3[i, beta != 0] <- beta1
    alpha3[i, alpha != 0] <- alpha1
  }
  beta <- as.vector(beta3)
  alpha <- as.vector(alpha3)
  return(list(beta = beta, alpha = alpha, U=U, fU = fU, fU.est= fU.est, B = B,
              lam1 = lambda_beta, lam2 = lambda_gamma, t = t))
}

data <- data.gener(n, p, q, beta.true, alpha.true)
Y <- data$Y; X <- data$XX; XX <- data$X; U <- data$U; fU <- data$fU;  IXX <- data$IXX
M <- length(n); p <- ncol(X)/M; q <- ncol(U); totaln <- sum(n)
Y.obs <- Y; X.obs <- X; fU.obs <- standardize(fU); IXX.obs <- IXX
Esti_sh_sp <- est.block(n, Y, X, XX, U, IXX, fU, p , eps1 = .001)



