library(ggplot2)
library(stats)
library(reshape2)
library(matrixStats)
library(compiler)
library(tseries)
library(standardize)
library(arrayhelpers)
library(matrixcalc)

Y_l <- function(X,lag){
    p <- lag
    X <- as.matrix(X)
    Q <- nrow(X)
    N <- ncol(X)
    Xlag <- matrix(0,Q,p*N)
    for (ii in 1:p){
        Xlag[(p+1):Q,(N*(ii-1)+1):(N*ii)]=X[(p+1-ii):(Q-ii),(1:N)]
    }
    return(Xlag)
}

OLSReg <- function(X,Y){
    A <- solve(t(X) %*% X) %*% t(X)%*%Y
    nA <- ncol(A)
    E <- Y - X %*% A
    e_r <- E
    Sigma2 <- t(e_r)%*%e_r/(L-p-p*M-1)
    Sigma00 <- matrix(0,nA,nA)
    Sigma00[1:M,1:M] <- Sigma2
    return(list(A=A,e_r=e_r,Sigma2=Sigma2))
}

Compa <- function(A){
    At <- t(A)[,2:nrow(A)]
    Bot <- cbind(diag(M*(p-1)),matrix(0,M*(p-1),M))
    compa <- rbind(At,Bot)
    return(compa)
}


irf <- function(B,smat,nstep){
    
    ### By:             As emerges from rfvar, neqn x nvar x lags array of rf VAR coefficients.
    ### smat:           nshock x nvar matrix of initial shock vectors.  To produce "orthogonalized
    ###                 impulse responses" it should have the property that crossprod(t(smat))=sigma,
    ###                 where sigma is the Var(u(t)) matrix and u(t) is the rf residual vector.  One
    ###                 way to get such a smat is to set smat=t(chol(sigma)).  To get the smat
    ###                 corresponding to a different ordering, use
    ###                 smat = t(chol(P %*% Sigma %*% t(P)) %*% P), where P is a permutation matrix.
    ###                 To get impulse responses for a structural VAR in the form A(L)y=eps, with
    ###                 Var(eps)=I, use B(L)=-A_0^(-1)A_+(L) (where A_+ is the coefficients on strictly
    ###                 positive powers of L in A), smat=A_0^(-1).
    ###                 In general, though, it is not required that smat be invertible.
    ### response:       nvar x nshocks x nstep array of impulse responses.
    ###
    ### Code written by Christopher Sims, based on 6/03 matlab code.  This version 3/27/04.
    ### Added dimension labeling, 8/02/04.
    
    ##-----debug--------
    ##browser()
    ##------------------ 
    neq <- dim(B)[1]
    nvar <- dim(B)[2]
    lags <- dim(B)[3]
    dimnB <- dimnames(B)
    if(dim(smat)[2] != dim(B)[2]) stop("B and smat conflict on # of variables")
    response <- array(0,dim=c(neq,nvar,nstep+lags-1));
    response[ , , lags] <- smat
    response <- aperm(response, c(1,3,2))
    irhs <- 1:(lags*nvar)
    ilhs <- lags * nvar + (1:nvar)
    response <- matrix(response, ncol=neq)
    B <- B[, , seq(from=lags, to=1, by=-1)]  #reverse time index to allow matrix multiply instead of loop
    B <- matrix(B,nrow=nvar)
    for (it in 1:(nstep-1)) {
        #browser()
        response[ilhs, ] <- B %*% response[irhs, ]
        irhs <- irhs + nvar
        ilhs <- ilhs + nvar
    }
    ## for (it in 2:nstep)
    ##       {
    ##         for (ilag in 1:min(lags,it-1))
    ##           response[,,it] <- response[,,it]+B[,,ilag] %*% response[,,it-ilag]
    ##       }
    dim(response) <- c(nvar, nstep + lags - 1, nvar)
    response <- aperm(response[ , -(1:(lags-1)), ], c(1, 3, 2)) #drop the zero initial conditions; array in usual format
    dimnames(response) <- list(dimnB[[1]], dimnames(smat)[[2]], NULL)
    ## dimnames(response)[2] <- dimnames(smat)[1]
    ## dimnames(response)[1] <- dimnames(B)[2]
    return(response)
}

# Forecast Variance Decompisitions 
# Motivated by Ambrogio Cesa-Bianchi's VAR Toolbox 
#- Ambrogio Cesa-Bianchi 2015. "VAR Toolbox", sites.google.com/site/ambropo/".
# For more technical summary on FEVD see James D. Hamilton - Time Series Analysis (1994)
FEVD <- function(B0,h,irfresults,Sigma2){
    PSI <-  array(0,c(M,M,h))
    ## Store multiplers from IRF
    for (jj in 1:nvar){
        PSI[,jj,] <- array(t(irfresults[,,jj]),c(1,M,h))
    }
    MSE <- array(0,c(M,M,h))
    MSE.j <- array(0,c(M,M,h))
    FEVD_mat <- array(0,c(h,M,M))
    SE <- matrix(0,h,M) 
    
    for(k in 1:M){
        
        # Error Forecasting a VAR - Hamilton(1994, p. 323,Eq. 11.5.1)
        MSE[,,1] = Sigma2
        
        for(a in 2:h){
            MSE[,,a] <- MSE[,,a-1] + PSI[,,a]%*%Sigma2%*%t(PSI[,,a])
        } 
        
        colu <- B0[,k]
        # Mean Square Error with orthogonalized disturbances 
        # Hamilton(1994, p. 324,Eq. 11.5.7)
        MSE.j[,,1] = colu%*%t(colu)
        for (zz in 2:h){
            MSE.j[,,zz] <- MSE.j[,,zz-1] + PSI[,,zz]%*%(colu %*% t(colu))%*%t(PSI[,,zz])
        }
        FEV.j <- MSE.j/MSE
        
        for (n in 1:h){
            for(q in 1:M){
                FEVD_mat[n,k,q] <- FEV.j[q,q,n]
                SE[n,] <- sqrt(t(diag(MSE[,,n])))
            }
        }
    }
    return(list(SE=SE,FEVD = FEVD_mat,FEV.j=FEV.j,PSI=PSI,MSE=MSE,MSE.j=MSE.j))
} 

# Historical Decomposition 
# Ambrogio Cesa-Bianchi 2015. "VAR Toolbox", https://github.com/ambropo/VAR-Toolbox.
# Technical Details in Burbidge and Harrison (1985)
HistoDecomp <- function(B0,E,X){
    p_m <- p*M 
    seps <- B0%*%t(E) # structural errors
    #nobs of observatiron
    H <- O +1
    beta <- X[,1:ncol(X)-1] # remove 
    B0_big <- matrix(0,p_m,M)
    B0_big[1:M,] <- B0
    Icomp <- cbind(diag(M),matrix(0,M,M*(p-1)))
    HDshock_big <- array(0,c(p_m,H,M))
    HDshock <- array(0,c(M,H,M))
    for (j in 1:M){
        seps_big <- matrix(0,M,H)
        seps_big[j,2:ncol(seps_big)] <- seps[j,]
        for (i in 2:H){
            HDshock_big[,i,j] <- B0_big%*%seps_big[,i] + compa%*%HDshock_big[,i-1,j]    
            HDshock[,i,j] <- Icomp%*%HDshock_big[,i,j]    
        }
    }
    PP <- O + p
    HD.Shock <- array(0,c(PP,M,M))
    for (i in 1:M){
        for (j in 1:M){
            HD.Shock[,j,i] = c(rep(NA,p), HDshock[i,(2:ncol(HDshock)),j])
        }
    }
    return(HD.Shock)
}    

bootstrap <- function(Y,E,Psi_i,reps,p,h,Irfstor,HorMat){
    for (i in 1:reps){
        if(i %% 500 == 0){
            
            cat("Simulation no.",i,"\n")}
        
        # NonParametric Bootstrap
        #Ur <-matrix(sample(E,length(E),replace = TRUE),PR,PC)
        #Yx <- matrix(sample(Psi_i,length(Psi_i),replace = TRUE),PR,PC)
        #Parametric Bootstrap
        Ur <- matrix(rnorm(PR*PC,0,1),PR,PC)
        Yx <- matrix(rnorm(PR*PC,0,1),PR,PC)
        
        eta <- matrix(rnorm(PR*PC,0,1),1,)
        
        Y <- Yx + Ur    
        
        Xlag <- Y_l(Y,p)
        Y <- Y[(p+1):nrow(Y),,drop=FALSE] 
        X <- cbind(Xlag[(p+1):nrow(Xlag),],1)
        
        # OLS Function for Bootstrap
        VAR_Est_b <- OLSReg(X,Y)
        A_b <- VAR_Est_b$A
        Sigma2_b <- VAR_Est_b$Sigma2
        B0 <- t(chol(Sigma2_b))
        
        phi_array_b <- array(0,c(M,M,p))
        for (k in 1:p){
            phi_array_b[,,k] <- t(A_b[((k-1)*M+1):(k*M),])
        }
        irfresults_b <- irf(B = phi_array_b,smat = B0,nstep = h)
        
        #Store Shocks for each horizon 
        for (m in 1:h){
            HorMat[,m] <- irfresults_b[,,m]
        }
        
        # Store Responses 
        Irfstor[i,] <- vec(HorMat)
        
    }    
    return(list(IRF=Irfstor))
}
