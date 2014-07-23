###############################################################################
# Load common dependencies.
# Systematic Investor Toolbox.
source('C:/Users/Vinicius/Google Drive/R/Finance/SIT.R')
# Data manipulation.
library('dplyr')
library('reshape2')
# Finance, Mathematics and Optimization.
library('corpcor')
library('lpSolve')
library('kernlab')
library('quadprog')
library('quantmod')
library('PerformanceAnalytics')
source('C:/Users/Vinicius/Google Drive/R/donlp2Control.R')
# Aesthetics and plotting.
library('colorspace')
library('ggplot2')
library('googleVis')
library('gridExtra')
library('RColorBrewer')
library('wq')

###############################################################################
# General purpose functions
alphaStream <- function
( # Computes models' alpha return streams and creates a wealth index for each of them.
  model.returns, 
  benchmark.returns
)
{
  beta <- as.vector(CAPM.beta(model.returns, benchmark.returns))
  
  beta.exposure <- model.returns
  n.cols <- dim(beta.exposure)[2]
  beta.exposure[] <- NA
  beta.exposure[, 1:n.cols] <- benchmark.returns
  beta.exposure <- beta.exposure * as.vector(beta)
  
  output <- list()
  output$ret <- model.returns - beta.exposure
  output$index <- wealthIndex(output$ret)
  return(output)
}

bt.prep2 <- function
(
  b,
  align = c('keep.all', 'remove.na'),
  dates = NULL,
  fill.gaps = F
)
{
  if( !exists('symbolnames', b, inherits = F) ) b$symbolnames = ls(b)
  symbolnames = b$symbolnames
  nsymbols = len(symbolnames)
  if( nsymbols > 1 ) {
    out = bt.merge(b, align, dates)
    for( i in 1:nsymbols ) {
      b[[ symbolnames[i] ]] =
        make.xts( coredata( b[[ symbolnames[i] ]] )[ out$date.map[,i],, drop = FALSE], out$all.dates)
      map.col = find.names('Close,Volume', colnames(b[[ symbolnames[i] ]]))
      if(fill.gaps & !is.na(map.col$Close)) {
        close = coredata(b[[ symbolnames[i] ]][,map.col$Close])
        n = len(close)
        last.n = max(which(!is.na(close)))
        close = ifna.prev(close)
        if(last.n + 5 < n) close[last.n : n] = NA
        b[[ symbolnames[i] ]][, map.col$Close] = close
        index = !is.na(close)
        if(!is.na(map.col$Volume)) {
          index1 = is.na(b[[ symbolnames[i] ]][, map.col$Volume]) & index
          b[[ symbolnames[i] ]][index1, map.col$Volume] = 0
        }
        for(j in colnames(b[[ symbolnames[i] ]])) {
          index1 = is.na(b[[ symbolnames[i] ]][,j]) & index
          b[[ symbolnames[i] ]][index1, j] = close[index1]
        }
      }
    }
  } else {
    if(!is.null(dates)) b[[ symbolnames[1] ]] = b[[ symbolnames[1] ]][dates,]
    out = list(all.dates = index.xts(b[[ symbolnames[1] ]]) )
  }
  b$dates = out$all.dates
  dummy.mat = matrix(double(), len(out$all.dates), nsymbols)
  colnames(dummy.mat) = symbolnames
  dummy.mat = make.xts(dummy.mat, out$all.dates)
  cl.mat = ad.mat =  vo.mat = dummy.mat
  b$weight = dummy.mat
  b$execution.price = dummy.mat
  for( i in 1:nsymbols ) {
    if( has.Cl( b[[ symbolnames[i] ]] ) ) {
      cl.mat[,i] = Cl( b[[ symbolnames[i] ]] );
    }
    
    if( has.Ad( b[[ symbolnames[i] ]] ) ) {
      ad.mat[,i] = Ad( b[[ symbolnames[i] ]] );
    }
    
    if( has.Vo( b[[ symbolnames[i] ]] ) ) {
      vo.mat[,i] = Vo( b[[ symbolnames[i] ]] );
    }
  }
  b$prices = cl.mat
  b$adjusted = ad.mat
  b$volume = vo.mat
}

bt.detail.summary <- function
(
  bt,
  trade.summary = NULL
)
{
  out.all = list()
  out = list()
  out$Period = join( format( range(index.xts(bt$equity)), '%b%Y'), ' - ')
  out$Cagr = compute.cagr(bt$equity)
  out$Sharpe = compute.sharpe(bt$ret) / 100
  out$DVR = compute.DVR(bt) / 100
  out$Volatility = compute.risk(bt$ret)
  out$MaxDD = compute.max.drawdown(bt$equity)
  out$AvgDD = compute.avg.drawdown(bt$equity)
  if( !is.null(trade.summary) ) {
    out$Profit.Factor = trade.summary$stats['profitfactor', 'All']
  }
  out$VaR = compute.var(bt$ret)
  out$CVaR = compute.cvar(bt$ret)
  out$Exposure = compute.exposure(bt$weight)
  out.all$System = lapply(out, function(x) if(is.double(x)) round(100*x,2) else x)
  if( !is.null(bt$trade.summary) ) trade.summary = bt$trade.summary
  out = list()
  if( !is.null(trade.summary) ) {
    out$Win.Percent = trade.summary$stats['win.prob', 'All']
    out$Avg.Trade = trade.summary$stats['avg.pnl', 'All']
    out$Avg.Win = trade.summary$stats['win.avg.pnl', 'All']
    out$Avg.Loss = trade.summary$stats['loss.avg.pnl', 'All']
    out = lapply(out, function(x) if(is.double(x)) round(100*x,1) else x)
    out$Best.Trade = max(as.double(trade.summary$trades[, 'return']))
    out$Worst.Trade = min(as.double(trade.summary$trades[, 'return']))
    out$WinLoss.Ratio = round( -trade.summary$stats['win.avg.pnl', 'All']/trade.summary$stats['loss.avg.pnl', 'All'] , 2)
    out$Avg.Len = round(trade.summary$stats['len', 'All'],2)
    out$Num.Trades = trade.summary$stats['ntrades', 'All']
  }
  out.all$Trade = out
  out = list()
  out$Win.Percent.Day = sum(bt$ret > 0, na.rm = T) / len(bt$ret)
  out$Best.Day = bt$best
  out$Worst.Day = bt$worst
  month.ends = endpoints(bt$equity, 'months')
  mret = bt$equity[month.ends,] / mlag(bt$equity[month.ends,], nlag=1) - 1
  out$Win.Percent.Month = sum(mret > 0, na.rm = T) / len(mret)
  out$Best.Month = max(mret, na.rm = T)
  out$Worst.Month = min(mret, na.rm = T)
  year.ends = endpoints(bt$equity, 'years')
  mret = bt$equity[month.ends,] / mlag(bt$equity[month.ends,], nlag=1) - 1
  out$Win.Percent.Year = sum(mret > 0, na.rm = T) / len(mret)
  out$Best.Year = max(mret, na.rm = T)
  out$Worst.Year = min(mret, na.rm = T)
  out.all$Period = lapply(out, function(x) if(is.double(x)) round(100*x,1) else x)
  return(out.all)
}

compute.cagr <- function(equity)
{
  as.double( last(equity)^(1/compute.nyears(equity)) - 1 )
}

envApply <- function
( # Applies a function to an environment's objects.
  environment,  # Environment selected.
  FUN,          # Function to be applied.
  ...           # Optional function arguments.
)
{
  environment <- as.list(environment)
  output <- lapply(environment, FUN, ...)
  output <- as.environment(output)
  return(output)  
}

envSubset <- function
( # Subsets a list of elements from a given environment.
  environment,  # Environment to be subset.
  subset        # List with elements that will be selected.
)
{
  output <- as.list(environment)[subset]
  output <- as.environment(output)
  return(output)
}

extractModelData <- function
( # Synthetize and consolidate specific data sets contained in 'model' objects.
  models, # List of objects generated by the 'bt.run' funcion.
  target.data=c('equity', 'ret') # Extract either the models' equity curve or return streams.
)
{
  target.data=target.data[1]
  counter <- 0
  for(i in 1:length(models)){
    if(counter == 0) {
      output <- models[[i]][[target.data]]
    } else {
      e <- models[[i]][[target.data]]
      output <- cbind(output, e)
    }
    counter <- counter + 1
  }
  names(output) <- names(models)
  return(output)
}

generate.ia <- function
( # Generate input assumptions with customized aspects
  data,             # list that contains OHLCV xts objects
  time.window = '', # use to specify timewindow for analysis 
  min.float = 0     # minimum float value that instrument must reach to qualify for calculations
)
{
  ###############################################################################
  # Data preparation
  # Extract prices
  data <- as.list(data)
  prices <- lapply(data, subset, select=c(4))
  prices <- do.call(merge, prices)
  prices <- na.locf(prices)
  colnames(prices) <- names(data)
  prices <- prices[ ,order(names(data))]
  prices <- prices[time.window]
  # Extract volume data
  volume <- lapply(data, subset, select=c(5))
  volume <- do.call(merge, volume)
  volume <- na.locf(volume)
  colnames(volume) <- names(data)
  volume <- volume[ ,order(names(data))]
  volume <- volume[time.window]
  # Remove all instruments with no data at the window's first data row
  n <- which(is.na(prices[1, ]))
  if(length(n)!=0){
    prices <- prices[ ,-n]
    volume <- volume[ ,-n]
  }
  # Compute instrument's float
  float <- prices * volume
  # Remove all instruments without a minimum float at the final datapoint
  i <- dim(float)[1]
  f <- which(float[i, ] > min.float)
  float <- float[ ,f]
  prices <- prices[ ,f]
  volume <- volume[ ,f]
  # Compute returns
  returns <- prices / mlag(prices) - 1
  returns <- na.omit(returns)
  returns[!is.finite(returns)] <- 0
  
  ###############################################################################
  # Generate input assumptions  
  ia <- list()
  ia$prices <- prices
  ia$volume <- volume
  ia$hist.returns <- returns
  ia$n <- ncol(ia$hist.returns)
  ia$index <- index
  ia$symbols <- colnames(ia$hist.returns)
  ia$risk <- apply(ia$hist.returns, 2, sd, na.rm = T)
  ia$correlation <- cor(ia$hist.returns, use='complete.obs',method='pearson')
  ia$cov <- ia$correlation * (ia$risk %*% t(ia$risk))
  ia$expected.return <- apply(ia$hist.returns, 2, mean, na.rm = T)
  return(ia)
}

marketStructure <- function
( # Extracts the market structure at a given point in time.  
  ia,             # Input assumptions generated with the 'create.ia' function
  threshold = 0.5 # Clustering algorithm correlation threshold
)
{
  # Generate instrument column.
  instrument.df <- as.data.frame(ia$symbols)
  colnames(instrument.df) <- c('instrument')
  
  # Generate time coordinate.
  t <- as.Date(index(ia$hist.returns)[dim(ia$hist.returns)[1]])
  time <- rep(t, dim(ia$hist.returns)[2])  
  
  # Market clusters analysis.
  # Generate coordinates for cluster plot.
  # Compute correlation and dissimilarity.
  correlation <- ia$correlation
  dissimilarity <- 1 - (correlation)
  distance <- as.dist(dissimilarity)
  xy <- cmdscale(distance)
  
  # Find actual clusters with the FTCA Algorithm and format data.
  clusters.df <- as.data.frame(cluster.group.FTCA(threshold)(ia))
  colnames(clusters.df) <- c('cluster')
  
  # Set up coordinates data frame.
  xy.df <- as.data.frame(as.matrix(-xy))
  colnames(xy.df) <- c('x', 'y')
  
  # Set up risk data frame.
  risk.df <- as.data.frame(ifna(ia$risk, 0))
  colnames(risk.df) <- c('risk')
  
  # Set up reward data frame.
  expected.return.df <- as.data.frame(ifna(ia$expected.return, 0))
  colnames(expected.return.df) <- c('expected.return')
  
  # Finish structure data frame
  structure.df <- cbind(instrument.df, time)
  structure.df <- cbind(structure.df, clusters.df)
  structure.df <- cbind(structure.df, xy.df)
  structure.df <- cbind(structure.df, risk.df)
  structure.df <- cbind(structure.df, expected.return.df)
  structure.df$instrument <- as.character(structure.df$instrument)
  rownames(structure.df) <- index(structure.df)
  return(structure.df)  
}

monthlyReturnsTable <- function
( # Outputs a data frame of monhtly returns. 
  equity  # xts object. Daily equity curve.
)
{
  equity = map2monthly(equity)
  dates = index.xts(equity)
  equity = coredata(equity)
  if(T) {
    month.ends = date.month.ends(dates)
    year.ends =  date.year.ends(dates[month.ends])
    year.ends = month.ends[year.ends]
    nr = len(year.ends) + 1
  } else {
    month.ends = unique(c(endpoints(dates, 'months'), len(dates)))
    month.ends = month.ends[month.ends>0]
    year.ends =  unique(c(endpoints(dates[month.ends], 'years'), len(month.ends)))
    year.ends = year.ends[year.ends>0]
    year.ends = month.ends[year.ends]
    nr = len(year.ends) + 1
  }
  temp = matrix( double(), nr, 12 + 2)
  rownames(temp) = c(date.year(dates[year.ends]), 'Avg')
  colnames(temp) = spl('Jan,Feb,Mar,Apr,May,Jun,Jul,Aug,Sep,Oct,Nov,Dec,Year,MaxDD')
  index = c(1, year.ends)
  for(iyear in 2:len(index)) {
    iequity = equity[ index[(iyear-1)] : index[iyear] ]
    iequity = ifna( ifna.prev(iequity), 0)
    temp[(iyear-1), 'Year'] = last(iequity, 1) / iequity[1] -1
    temp[(iyear-1), 'MaxDD'] = min(iequity / cummax(iequity) - 1, na.rm = T)
  }
  index = month.ends
  monthly.returns = c(NA, diff(equity[index]) / equity[index[-len(index)]])
  index = date.month(range(dates[index]))
  monthly.returns = c( rep(NA, index[1]-1), monthly.returns, rep(NA, 12-index[2]) )
  temp[1:(nr - 1), 1:12] = matrix(monthly.returns, ncol=12, byrow = T)
  temp = ifna(temp, NA)
  temp[nr,] = apply(temp[-nr,], 2, mean, na.rm = T)
  temp <- round(temp*100, digits=2)
  
  output <- as.data.frame(ifna(temp, 0))
  return(output)
}

performanceTable <- function
(
  models  # Object which contains backtests generate by 'bt.run' functions
)
{
  output <- data.frame()
  for( i in 1:len(models) ) {
    output <- rbind(output, as.data.frame(bt.detail.summary(models[[ i ]])$System))
  }
  output <- output[, -1]
  
  model.names <- as.data.frame(names(models))
  colnames(model.names) <- 'model.names'
  
  turnover <- as.data.frame(sapply(models, compute.turnover, data))
  turnover <- round(turnover, digits=2)
  colnames(turnover) <- 'Turnover'
  
  output <- cbind(output, turnover)
  output <- cbind(model.names, output)
  rownames(output) <- index(output)
  
  time <- rep(1, dim(output)[1])
  output <- cbind(output, time)
  return(output)
}

regressedAnnualReturn <- function
( # Function to compute the regressed annual return of an xts object
  xts.prices, # 'xts.prices must be an xts object of prices
  n = 252, 
  scale = 252 # daily scale = 252, monthly scale = 12, quarterly scale = 4
)
{
  Ra <- log10(xts.prices)
  Rb <- row(xts.prices)
  
  rar <- runCov(Ra, Rb, n)/runVar(Rb, n = n)
  rar <- ((1+rar)^scale-1)
  rar <- rar * 100
  colnames(rar) <- 'RAR'
  
  return(rar)
}

rownamesToColumn <- function
(
  df, 
  new.column.name=''
)
{
  output <- as.data.frame(cbind(rownames(df), df))
  rownames(output) <- index(df)
  colnames(output)[1] <- new.column.name
  return(output)
}

tradeSummaryTable <- function
( # Generates a data frame suitable for googleVis plotting
  trades # '$trade.summary$trades' object generated by the 'bt.run' functions
)
{
  output <- as.data.frame(trades)
  output[, c(1:2, 5:7)] <- sapply(output[, c(1:2, 5:7)], as.character)
  output[, c(2, 5:7)] <- sapply(output[, c(2, 5:7)], as.numeric)
  output[, 3:4] <- sapply(output[, 3:4], as.character)
  output[, 3:4] <- lapply(output[, 3:4], as.Date, format='%Y-%m-%d')
  return(output)
}

wealthIndex <- function
( # Creates a wealth index out of a set of return streams.
  return.stream  # Input return stream(s).
)
{
  output <- cumprod(1 + return.stream)
  colnames(output) <- names(return.stream)
  return(output)  
}

xtsMelt <- function
( # Converts and melts xts objects into a data frame suitable for ggplot and other plotting methods.
  xts.object  
)
{
  series.names <- colnames(xts.object)
  output <- xtsToDataFrame(xts.object)
  output <- melt(output, id.var="time")
  return(output)
}

xtsToDataFrame <- function
( # Converts xts object to data frame. First column will contains its dates.
  xts.object
)
{
  output <- as.data.frame(xts.object)
  output <- cbind(rownames(output), output)
  rownames(output) <- index(output)
  colnames(output)[1] <- 'time'
  output$time <- as.Date(as.character(output$time), format='%Y-%m-%d')
  return(output)  
}

###############################################################################
# Plotting functions.

###############################################################################
# ggplot2.
ggSingleModelReport <- function
( # Generates a performance report of models based on ggplot2.
  bt,                    # Assumes a single model is loaded in.
  benchmark.ret=NULL,    # Benchmark returns for CAPM analysis.
  capm.scale=252         # Time scale for CAPM analysis. Daily = 252, monthly = 12, quarterly = 4.
)
{
  # Extract model returns for manipulation.
  ret <- extractModelData(bt, target.data='ret')
  colnames(ret) <- 'model'
  
  # PERFORMANCE TABLE.
  # Setup performance table data frame.
  perf <- performanceTable(bt)
  perf$model.names <- 'model'
  perf <- melt(perf, id.vars='model.names')
  # Setup graphical output.
  perf.table <- ggplot(perf, 
                       aes(x=variable, y=model.names))
  perf.table <- perf.table + geom_text(aes(label=value, fontface=2, size=8))
  perf.table <- perf.table + ylab('') + xlab('')
  perf.table <- perf.table + theme(legend.position='none')
  
  # TRADE STATISTICS TABLE.
  # Setup dataframe.
  trades.stats <- as.data.frame(t(bt[[1]]$trade.summary$stats))
  trades.stats[, c(2, 4, 5, 6, 7)] <- trades.stats[, c(2, 4, 5, 6, 7)] * 100
  trades.stats <- round(trades.stats, digits=2)
  trades.stats <- rownamesToColumn(trades.stats, new.column.name='direction')
  trades.stats <- melt(trades.stats, id.vars='direction')
  # Setup graphical output.
  trades.stats.table <- ggplot(trades.stats, 
                               aes(x=variable, y=direction))
  trades.stats.table <- trades.stats.table + geom_text(aes(label=value, fontface=2, size=8))
  trades.stats.table <- trades.stats.table + ylab('') + xlab('')
  trades.stats.table <- trades.stats.table + theme(legend.position='none')
  
  # MONTHLY RETURNS TABLE.
  # Construct table of model monthly returns.
  monthly <- monthlyReturnsTable(extractModelData(bt, target.data='equity'))
  monthly <- monthly[rev(rownames(monthly)), ]
  monthly <- melt(as.matrix(monthly))
  # Setup graphical output.
  monthly.table <- ggplot(data=monthly, aes(x=factor(Var2), y=Var1, fill=value)) + geom_raster()
  monthly.table <- monthly.table + labs(fill='Return (%)')
  monthly.table <- monthly.table + geom_text(aes(label=value), size=4)
  monthly.table <- monthly.table + xlab(label=NULL) +   ylab(label=NULL)
  monthly.table <- monthly.table + theme_bw()
  monthly.table <- monthly.table + theme(legend.position = 'none')
  monthly.table <- monthly.table + scale_fill_gradient2()
  
  # If benchmark is loaded run value added analysis.
  if(is.xts(benchmark.ret)){
    # Construct CAPM stats table.
    capm <- table.CAPM(ret, benchmark.ret, scale=capm.scale, digits=4)
    capm <- as.data.frame(t(capm))
    capm <- cbind(rownames(capm), capm)
    rownames(capm) <- index(capm)
    colnames(capm)[1] <- 'model'
    capm[1] <- 'model'
    capm <- melt(capm, id.vars='model')
    # Setup graphical output.
    capm.table <- ggplot(capm, 
                         aes(x=variable, y=model))
    capm.table <- capm.table + geom_text(aes(label=value, fontface=2, size=8))
    capm.table <- capm.table + ylab('') + xlab('')
    capm.table <- capm.table + theme(legend.position='none')
    
    # Extract alpha returns.
    alpha.ret <- alphaStream(ret, benchmark.ret)$ret
    
    # Join model, benchmark and model return streams.
    ret <- cbind(ret, benchmark.ret)
    ret <- cbind(ret, alpha.ret)
    colnames(ret) <- spl('model,benchmark,alpha')
  }
  
  # EQUITY AND DRAWDOWN CHART.
  # Convert returns into a wealth index and drawdowns.
  wealth <- xtsMelt(log(wealthIndex(ret)))
  wealth$type <- 'Wealth'
  dd <- xtsMelt(Drawdowns(ret))
  dd$type <- 'Drawdowns'
  df <- rbind(wealth, dd)
  df$type <- factor(df$type, levels=c('Wealth', 'Drawdowns'))
  # Setup graphical output.
  chart <- ggplot(df, 
                  aes(x=time, y=value, 
                      group=variable, colour=variable))
  chart <- chart + geom_line()
  chart <- chart + facet_grid(type~ ., scales = 'free_y')
  chart <- chart + geom_hline(yintercept = 0, size = 0.5, colour = 'black')
  chart <- chart + ylab('') + xlab('')
  chart <- chart + theme(legend.title = element_blank()
                         , legend.position = c(0,1)
                         , legend.justification = c(0,1)
                         , legend.background = element_rect()
                         , legend.text = element_text(size=8))
  # Call output
  layOut(list(chart, 1:3, 1),   # takes three rows and the first column
         list(perf.table, 1, 2),    # next three are on separate rows
         list(capm.table, 2,2), 
         list(trades.stats.table, 3,2))
  monthly.table  
}

ggMonthlyReturnsTable <- function
( # Outputs a ggplot table of monthly returns.
  monthlyReturnsTable.df  # Object created with the 'monthlyReturnsTable'.
)
{
  input <- monthlyReturnsTable.df[rev(rownames(monthlyReturnsTable.df)), ]
  input <- melt(as.matrix(input))
  
  output <- ggplot(data=input, aes(x=factor(Var2), y=Var1, fill=value)) + geom_raster()
  output <- output + labs(fill='Return (%)')
  output <- output + geom_text(aes(label=value), size=4)
  output <- output + xlab(label=NULL) +   ylab(label=NULL)
  output <- output + theme_bw()
  output <- output + theme(legend.position = 'none')
  output <- output + scale_fill_gradient2()
  return(output)
}

ggMultiModelReport <- function
( # Generates a performance report of models based on ggplot2.
  models
)
{
  # First order all models alphabetically.
  models <- models[ls(models)]
  
  # Extract model returns.
  ret <- extractModelData(models, target.data='ret')
  
  # Convert returns into a wealth index and drawdowns.
  wealth <- xtsMelt(log(wealthIndex(ret)))
  wealth$type <- 'Wealth'
  dd <- xtsMelt(Drawdowns(ret))
  dd$type <- 'Drawdowns'
  df <- rbind(wealth, dd)
  df$type <- factor(df$type, levels=c('Wealth', 'Drawdowns'))
  
  # Construct chart.
  chart <- ggplot(df, 
                  aes(x=time, y=value, 
                      group=variable, colour=variable))
  chart <- chart + geom_line()
  chart <- chart + facet_grid(type~ ., scales = 'free_y')
  chart <- chart + geom_hline(yintercept = 0, size = 0.5, colour = 'black')
  chart <- chart + ylab('') + xlab('')
  chart <- chart + theme(legend.title = element_blank()
                         , legend.position = c(0,1)
                         , legend.justification = c(0,1)
                         , legend.background = element_rect()
                         , legend.text = element_text(size=8))
  
  # Construct performance table.
  df <- performanceTable(models)
  df$model.names <- as.character(df$model.names)
  df <- melt(df, id.vars='model.names')
  
  # Construct table.
  table <- ggplot(df, 
                  aes(x=variable, y=model.names))
  table <- table + geom_text(aes(label=value, colour=model.names, fontface=2, size=8))
  table <- table + ylab('') + xlab('')
  table <- table + theme(legend.position='none')
  
  grid.arrange(chart, table, ncol=2)
}

###############################################################################
# googleVis.
gvisBtTransitionMap <- function
(
  weight,  # Object which contains backtest weights generated by the 'bt.run' functions
  stack=TRUE,       # Stack plots
  pane.width= 1300, # Pane width in pixels
  pane.height=600,  # Pane height in pixels
  title='transition map'
)
{
  # Format data into a gVis readable format
  weight.df <- as.data.frame(round(weight*100, digits=4))
  #weight.df[which(is.na(weight.df[, 1])), ] <- 0
  
  symbols <- colnames(weight.df)
  time.df <- rownames(weight.df)
  
  rownames(weight.df) <- index(weight.df)
  weight.df <- cbind(time.df, weight.df)
  
  # Construct chart
  output <- gvisAreaChart(weight.df, 
                          xvar='time.df', yvar=symbols, 
                          options=list(
                            hAxis="{gridlines:{count:0}, 
                            title:'Portfolios', 
                            titleTextStyle: {fontSize: 16}}", 
                            vAxis="{gridlines:{count:15}, 
                            title:'Weights', 
                            titleTextStyle: {fontSize: 16}}", 
                            areaOpacity=0.25, 
                            focusTarget='category', 
                            isStacked=stack, 
                            fontName='Times New Roman', 
                            fontSize=10, 
                            lineWidth=0.5, 
                            title=title, 
                            titleTextStyle='{fontSize: 16}', 
                            theme="{chartArea: {width: '80%', height: '80%'}, 
                            legend: {position: 'right', textStyle: {fontSize: 9}}, 
                            titlePosition: 'out', 
                            axisTitlesPosition: 'out', 
                            hAxis: {textPosition: 'out'}, 
                            vAxis: {textPosition: 'out'}}", 
                            width=pane.width, height=pane.height)
                          )
  return(output)
}

gvisChart <- function
( # Function to create a simple chart of xts objects with the Google Charts API
  xts.prices # 'xts.prices' parameter must be a xts object
)
{
# Data frame conversion and formatting
  p <- xts.prices
  df <- as.data.frame(p)
  df$dates <- rownames(df)
  rownames(df) <- 1:nrow(df)
  df$dates <- as.Date(df$dates)
  
  series.count <- dim(df)[2] - 1
  series.names <- colnames(df)
  series.names <- series.names[-dim(df)[2]]  
  
  price.data = reshape(df, 
                       idvar="Date", 
                       times=series.names, 
                       timevar="Type", 
                       varying=series.names, 
                       v.names="Value", 
                       direction="long")
  
##############################################################################
# Graphical output preparation
# Construct plots
  price.plot <- gvisAnnotatedTimeLine(price.data, 
                                      datevar="dates", numvar="Value", idvar="Type", 
                                      options=list(
                                        width=1300, height=600, 
                                        scaleType='maximized'), 
                                      chartid='Prices')
  
##############################################################################
# Final result
  plot(price.plot)
}

gvisCustomTable <- function
(
  custom.table.df,  # Data frame generated to be converted to a table.
  pane.width= 1300, # Pane width in pixels.
  pane.height=600   # Pane height in pixels.
)
{
  output <- gvisTable(custom.table.df, 
                      options=list(
                        width=pane.width, height=pane.height)
  )
  return(output)
}

gvisDensityPlot <- function
( # Generates a density plot of input object.
  input, 
  granularity=0.01, 
  pane.width= 1300, # Pane width in pixels.
  pane.height=600   # Pane height in pixels.
)
{
  hist.breaks <- seq(min(input), max(input)+granularity, by=granularity)
  hist.breaks <- round(hist.breaks, digits=4)
  input.hist <- lapply(input, hist, breaks=hist.breaks, plot=F)
  
  counter <- 0
  for(i in 1:length(input.hist)){
    if(counter == 0) {
      density <- input.hist[[i]]$density
    } else {
      d <- input.hist[[i]]$density
      density <- cbind(density, d)
    }
    counter <- counter + 1
  }
  
  density <- as.data.frame(density)
  density[dim(density)[1] + 1, ] <- 0
  names(density) <- names(input.hist)
  density <- cbind(hist.breaks, density)
  density$hist.breaks <- as.character(density$hist.breaks)
  
  output <- gvisLineChart(density, xvar='hist.breaks', yvar=names(density)[-1], 
                          options=list(
                            hAxis="{gridlines:{count:0}, 
                            title:'Breaks', 
                            titleTextStyle: {fontSize: 16}}", 
                            vAxis="{gridlines:{count:15}, 
                                    title:'Density', 
                                    titleTextStyle: {fontSize: 16}}", 
                            curveType='function', 
                            fontName='Times New Roman', 
                            fontSize=10, 
                            lineWidth=1, 
                            pointSize=0, 
                            title='Density Plot', 
                            titleTextStyle='{fontSize: 16}', 
                            theme="{chartArea: {width: '80%', height: '80%'}, 
                                    legend: {position: 'right', 
                                    textStyle: {fontSize: 9}}, 
                                    titlePosition: 'out', 
                                    axisTitlesPosition: 'out', 
                                    hAxis: {textPosition: 'out'},
                                    vAxis: {textPosition: 'out'}}", 
                            width=pane.width, height=pane.height)
                          )
  return(output)
}

gvisEFScatterPlot <- function
( # Generates a googleVis object of efficient frontiers scatter plots
  ia,  # Input assumptions generated with customized 'generate.ia' function
  efs, # Efficient frontier. List of objects generated by SIT's 'portopt' function
  portfolio.risk.fn=portfolio.risk,  # One of SIT's portfolio risk functions
  pane.width= 1300, # Pane width in pixels
  pane.height=600   # Pane height in pixels
)
{
  # Assign risk label
  risk.label <- as.character(substitute(portfolio.risk.fn))
  
  # Setup instrument data frames
  n = ia$n
  x = match.fun(portfolio.risk.fn)(diag(n), ia)
  y = ia$expected.return
  
  # Setup efficient frontiers' data frames
  efs.df <- matrix(nrow=1, ncol=len(efs)+1)
  
  # Get instrument's risk parameters
  instrument.risk <- match.fun(portfolio.risk.fn)(diag(n), ia)
  
  # Get efficient frontiers' risk parameters
  frontier.risk <- matrix()
  for(i in len(efs):1) {
    ef <- efs[[ i ]]
    x <- as.matrix(match.fun(portfolio.risk.fn)(ef$weight, ia))
    frontier.risk <- rbind(frontier.risk, x)
  }
  frontier.risk <- frontier.risk[-1, ]
  
  # Combine both
  risk <- c(instrument.risk, frontier.risk)
  
  # Transform into data frame
  efs.df <- as.data.frame(risk)
  
  # Assign expected returns parameters
  for(i in 1:length(ia$symbols)){
    efs.df[i, i+1] <- as.data.frame(ia$expected.return)[i, 1]
  }
  colnames(efs.df) <- c('risk', ia$symbols)
  
  # Assign efficient frontiers' returns
  start <- length(ia$symbols)+1
  for(i in len(efs):1) {
    ef <- efs[[ i ]]
    y <- matrix(nrow=nrow(efs.df), ncol=1)
    frontier.returns <- as.matrix(ef$return)
    l <- len(frontier.returns)
    
    y[(start):(start+l-1), ] <- frontier.returns
    colnames(y) <- ef$name
    
    start <- start + len(frontier.returns)
    efs.df <- cbind(efs.df, y)
  }
  efs.df <- as.data.frame(efs.df)
  efs.df <- efs.df * 100
  
  # Format efficient frontier line series
  count <- as.integer(length(ia$symbols))
  ef.format <- character()
  for(i in 1:length(efs)){
    format <- paste(count, ':{pointSize: 0, visibleInLegend: false}, ', sep='')
    ef.format <- paste(ef.format, format)
    count <- count + 1
  }
  ef.format <- substring(ef.format, 2, nchar(ef.format)-2)
  ef.format <- paste('{', ef.format, '}', sep='')
  
  # Format horizontal axis
  hAxis.format <- paste('{gridlines:{count:15}, ', 
                        'title:', risk.label, ', ', 
                        'titleTextStyle: {fontSize: 16}}', sep='')
  
  # Construct chart
  scatter.plot <- gvisScatterChart(efs.df, 
                                   options=list(
                                     hAxis="{gridlines:{count:15}, 
                                     title:'Risk', 
                                     titleTextStyle: {fontSize: 16}}", 
                                     vAxis="{gridlines:{count:15}, 
                                     title:'Return', 
                                     titleTextStyle: {fontSize: 16}}", 
                                     curveType='function', 
                                     fontName='Times New Roman', 
                                     fontSize=10, 
                                     lineWidth=1, 
                                     pointSize=7, 
                                     series=ef.format, 
                                     title=paste(risk.label, ' vs. return', sep=''), 
                                     titleTextStyle='{fontSize: 16}', 
                                     theme="{chartArea: {width: '80%', height: '80%'}, 
                                     legend: {position: 'right', 
                                     textStyle: {fontSize: 9}}, 
                                     titlePosition: 'out', 
                                     axisTitlesPosition: 'out', 
                                     hAxis: {textPosition: 'out'},
                                     vAxis: {textPosition: 'out'}}", 
                                     width=pane.width, height=pane.height))
  return(scatter.plot)  
}

gvisEFTransitionMap <- function
( # Generates a googleVis object of efficient frontiers transition maps
  ef, # Efficient frontier. Object generated by SIT's 'portopt' function
  stack=TRUE,       # Stack plots
  pane.width= 1300, # Pane width in pixels
  pane.height=600   # Pane height in pixels
)
{
  weight.df <- as.data.frame(round(ef$weight*100, digits=4))
  
  # Setup data frame
  symbols <- which(colnames(f.sd$weight) != '')
  weight.df <- weight.df[, symbols]
  remove <- names(weight.df[ , colSums(weight.df)==0])
  remove <- which(colnames(weight.df) %in% remove)
  if(length(remove) > 0) {weight.df <- weight.df[, -remove]}
  symbols <- colnames(weight.df)
  weight.df$portfolios <- as.character(rownames(weight.df))
  
  # Construct chart
  transition.map <- gvisAreaChart(weight.df, 
                                  xvar='portfolios', yvar=symbols, 
                                  options=list(
                                    hAxis="{gridlines:{count:0}, 
                                    title:'Portfolios', 
                                    titleTextStyle: {fontSize: 16}}", 
                                    vAxis="{gridlines:{count:15}, 
                                    title:'Weights', 
                                    titleTextStyle: {fontSize: 16}}", 
                                    areaOpacity=0.25, 
                                    focusTarget='category', 
                                    isStacked=stack, 
                                    fontName='Times New Roman', 
                                    fontSize=10, 
                                    lineWidth=0.5, 
                                    title=paste('transition map for ', ef$name, sep=''), 
                                    titleTextStyle='{fontSize: 16}', 
                                    theme="{chartArea: {width: '80%', height: '80%'}, 
                                    legend: {position: 'right', textStyle: {fontSize: 9}}, 
                                    titlePosition: 'out', 
                                    axisTitlesPosition: 'out', 
                                    hAxis: {textPosition: 'out'}, 
                                    vAxis: {textPosition: 'out'}}", 
                                    width=pane.width, height=pane.height))
  return(transition.map)
}

gvisInstrumentInspection <- function
( # Overlays trades on price plot of a given instrument
  bt=NULL,                  # backtest whose trades we want to inspect
  bt.symbol=NULL,           # symbol to plot trades over
  prices,                   # xts object which may contain prices and other indicator overlays
  gvis.colors='',           # color to apply to chart items. use gvis formatting: "['color list']"
  annotations=TRUE,         # Display annotations
  range.selector=TRUE,      # Display range selector
  pane.width= 1300,         # Pane width in pixels
  pane.height=600           # Pane height in pixels
)
{ # Function core
  # Setup main data frames
  prices.names <- colnames(prices)
  prices.df <- xtsToDataFrame(prices)
  input.df <- prices.df
  
  input <- reshape(input.df, 
                   idvar='time', 
                   times=prices.names, 
                   timevar='Type', 
                   varying=prices.names, 
                   v.names='Value', 
                   direction='long')
  
  if(is.null(bt) == FALSE){
    weight.df <- bt$weight[, bt.symbol]
    weight.df <- xtsToDataFrame(weight.df)
    weight.df <- mutate(weight.df, trades='')
    
    w <- weight.df[, bt.symbol]
    
    weight.df$trades <- ifelse(w>0 & Lag(w)==0, 'Open Long', '')
    weight.df$trades <- ifelse(w>0 & Next(w)==0, 'Close Long', weight.df$trades)
    weight.df$trades <- ifelse(w<0 & Lag(w)==0, 'Open Short', weight.df$trades)
    weight.df$trades <- ifelse(w<0 & Next(w)==0, 'Close Short', weight.df$trades)
    
    position.df <- weight.df[, -2]
    colnames(position.df) <- c('time', 'trades')
    position.df <- filter(position.df, trades != '')
    subset1 <- input$time %in% position.df$time
    subset2 <- input$Type == bt.symbol
    input <- mutate(input, trades='')
    input[subset1 & subset2, ]$trades <- as.character(position.df$trades)   
    
    title <- 'trades'
  } else {
    title <- ''
  }
  
  output <- gvisAnnotatedTimeLine(input,
                                  datevar='time', numvar="Value", idvar="Type", 
                                  titlevar=title, 
                                  options=list(
                                    annotationsWidth=15, 
                                    colors=gvis.colors, 
                                    displayAnnotations=annotations, 
                                    displayRangeSelector=range.selector, 
                                    scaleType='maximized', 
                                    width=pane.width, height=pane.height
                                    )
                                  )
  return(output)
}

gvisLinePlot <- function
(
  input.df,                 # Data frame. First column must contain dates
  range.selector=FALSE,     # Display range selector
  zoom.buttons=TRUE,        # Display zoom buttons
  pane.width= 1300,         # Pane width in pixels
  pane.height=600           # Pane height in pixels
)
{
  x.name <- names(input.df)[1]
  y.name <- names(input.df)[-1]
  
  input <- reshape(input.df, 
                   idvar=x.name, 
                   times=y.name, 
                   timevar="Type", 
                   varying=y.name, 
                   v.names="Value", 
                   direction="long")
  
  output <- gvisAnnotatedTimeLine(input, 
                                  datevar=x.name, numvar="Value", idvar="Type",
                                  options=list(
                                    displayRangeSelector=range.selector, 
                                    displayZoomButtons=zoom.buttons, 
                                    scaleType='maximized', 
                                    width=pane.width, height=pane.height
                                    )
                                  )
  return(output)
}

gvisMarketStructure <- function
( # Generates a googleVis Motion Chart with market structure data
  market.structure, # Data frame generated with the custom "marketStructure" function
  pane.width= 1300, # Pane width in pixels
  pane.height=600   # Pane height in pixels
)
{ 
  market.structure.df <- market.structure
  
  ###############################################################################
  # Create googleVis Motion Chart
  # Construct plot
  structure <- gvisMotionChart(market.structure.df, 
                               idvar='instrument', 
                               timevar='time', 
                               xvar='x', yvar='y', 
                               colorvar='risk', 
                               sizevar='float', 
                               options=list(
                                 hAxis='{gridlines:{count:15}}', 
                                 vAxis='{gridlines:{count:15}}', 
                                 fontName='Times New Roman', 
                                 fontSize=10, 
                                 sizeAxis='{minSize:10, maxSize:20}', 
                                 titleTextStyle='{fontSize: 16}', 
                                 theme="{chartArea: {width: '80%', height: '80%'}, 
                                        legend: {position: 'right'}, 
                                        titlePosition: 'out', 
                                        axisTitlesPosition: 'out', 
                                        hAxis: {textPosition: 'out'}, 
                                        vAxis: {textPosition: 'out'}}", 
                                 width=pane.width, height=pane.height), 
                               chartid='Market_Structure')
  return(structure)
}

gvisMultiModelReport <- function
( # Generates a performance report of models based on googleVis.
  models, 
  pane.width=1300,         # Pane width in pixels
  pane.height=500,          # Pane height in pixels
  table.height=140,         # Performance table height in pixels
  range.selector=TRUE,     # Display range selector
  zoom.buttons=TRUE        # Display zoom buttons
)
{
  perf.table <- performanceTable(models)
  perf.table.plot <- gvisCustomTable(perf.table, 
                                     pane.height=table.height, pane.width=pane.width)
  
  equity.df <- log(extractModelData(models)) * 100
  equity.df <- xtsToDataFrame(equity.df)
  equity.plot <- gvisLinePlot(equity.df, range.selector=range.selector, zoom.buttons=zoom.buttons, 
                               pane.height=pane.height, pane.width=pane.width)
  
  dd.df <- extractModelData(models, target.data='ret')
  dd.df <- Drawdowns(dd.df) * 100
  dd.df <- xtsToDataFrame(dd.df)
  
  dd.plot <- gvisLinePlot(dd.df, range.selector=range.selector, zoom.buttons=zoom.buttons, 
                           pane.height=pane.height, pane.width=pane.width)
  
  output <- gvisMerge(perf.table.plot, equity.plot)
  output <- gvisMerge(output, dd.plot, chartid='Multi_Strategy_Report')
  return(output)  
}

gvisPerformanceMotion <- function
( # Generates a googleVis Motion Chart with performance report data
  performanceTable.output, 
  pane.width= 1300, # Pane width in pixels
  pane.height=600   # Pane height in pixels
)
{
  output <- gvisMotionChart(performanceTable.output, 
                            idvar='model.names', 
                            timevar='time', 
                            xvar='Volatility', yvar='Cagr', 
                            colorvar='Sharpe', 
                            sizevar='Turnover', 
                            options=list(
                              hAxis='{gridlines:{count:15}}', 
                              vAxis='{gridlines:{count:15}}', 
                              fontName='Times New Roman', 
                              fontSize=10, 
                              sizeAxis='{minSize:10, maxSize:20}', 
                              titleTextStyle='{fontSize: 16}', 
                              theme="{chartArea: {width: '80%', height: '80%'}, 
                              legend: {position: 'right'}, 
                              titlePosition: 'out', 
                              axisTitlesPosition: 'out', 
                              hAxis: {textPosition: 'out'}, 
                              vAxis: {textPosition: 'out'}}", 
                              width=pane.width, height=pane.height)
  )
  return(output)  
}

gvisPerformanceReport <- function
( # Function to create performance reports and charts with the Google Charts API
  xts.prices, # 'xts.prices must be an xts object of prices
  returns.type=c('arithmetic', 'log'), 
  scale=252
)
{
  ###############################################################################
  # Compute performance data
  p <- xts.prices
  instrument.names <- names(p)
  ret <- do.call(merge, lapply(p, dailyReturn, type=returns.type))
  ret[is.na(ret)] <- 0
  colnames(ret) <- instrument.names
  cum.ret <- cumprod(1 + ret)
  cum.ret <- cum.ret - 1
  dd <- Drawdowns(ret)
  
  ###############################################################################
  # Compute summary performance statistics
  cagr <- Return.annualized(ret, scale=scale, geometric=TRUE)
  std.dev <- sd.annualized(ret, scale=scale)
  maxdd <- maxDrawdown(ret)
  sharpe <- SharpeRatio.annualized(ret, Rf=0, scale=scale, geometric = TRUE)
  mar.ratio <- cagr / maxdd
  
  ###############################################################################
  # Convert data to a format readable by googleVis
  # Set up performance metrics table
  perf.table <- matrix(c(cagr, std.dev, maxdd, sharpe, mar.ratio), nrow=dim(p)[2], ncol=5)  
  perf.table <- as.data.frame(perf.table)
  perf.table <- cbind(perf.table, instrument.names)
  perf.table.columns <- dim(perf.table)[2]
  perf.table.rows <- dim(perf.table)[1]
  perf.table <- perf.table[, c(perf.table.columns, 1:perf.table.columns-1)]
  rownames(perf.table) <- 1:perf.table.rows
  colnames(perf.table) <- c('Instrument', 'CAGR', 'Std. Dev', 'Max DD', 'Sharpe', 'MAR Ratio')
  
  # Data frame conversion, formatting and reshaping
  # Cummulative returns
  cum.ret.df <- as.data.frame(cum.ret)
  cum.ret.df.rows <- dim(cum.ret.df)[1]
  cum.ret.df.columns <- dim(cum.ret.df)[2]
  cum.ret.df$dates <- rownames(cum.ret.df)
  rownames(cum.ret.df) <- 1:nrow(cum.ret.df)
  cum.ret.df$dates <- as.Date(cum.ret.df$dates)
  
  cum.ret.molten = reshape(cum.ret.df, 
                           idvar="Date", 
                           times=instrument.names, 
                           timevar="Type", 
                           varying=list(instrument.names), 
                           v.names="Value", 
                           direction="long")
  
  # Drawdowns
  dd.df <- as.data.frame(dd*100)
  dd.df.rows <- dim(dd.df)[1]
  dd.df.columns <- dim(dd.df)[2]
  dd.df$dates <- rownames(dd.df)
  rownames(dd.df) <- 1:nrow(dd.df)
  dd.df$dates <- as.Date(dd.df$dates)
  
  dd.molten = reshape(dd.df, 
                      idvar="Date", 
                      times=instrument.names, 
                      timevar="Type", 
                      varying=list(instrument.names), 
                      v.names="Value", 
                      direction="long")
  
  ##############################################################################
  # Graphical output preparation
  # Construct performance table visualization
  perf.table.plot <- gvisTable(perf.table, 
                               options=list(
                                 width=450, height=600), 
                               formats=list('CAGR'='#.##%', 
                                            'Std. Dev'='#.##%', 
                                            'Max DD'='#.##%', 
                                            'Sharpe'='#.##', 
                                            'MAR Ratio'='#.##')
  )
  
  # Construct plots
  # Cummulative returns
  cum.ret.plot <- gvisAnnotatedTimeLine(cum.ret.molten, 
                                        datevar="dates", numvar="Value", idvar="Type", 
                                        options=list(
                                          width=850, height=400, 
                                          fill=0, 
                                          scaleType='maximized', 
                                          displayRangeSelector=FALSE)
  )
  
  # Drawdowns
  dd.plot <- gvisAnnotatedTimeLine(dd.molten, 
                                   datevar="dates", numvar="Value", idvar="Type", 
                                   options=list(
                                     width=850, height=190, 
                                     scaleType='allmaximized',
                                     displayRangeSelector=FALSE, 
                                     displayZoomButtons=FALSE)
  )
  
  # Merge plots
  finalPlot <- gvisMerge(cum.ret.plot, dd.plot)
  finalPlot <- gvisMerge(finalPlot, perf.table.plot, horizontal=TRUE, chartid='Performance_Report')
  
  #############################################################################
  # Final result
  plot(finalPlot)
}

gvisSingleModelReport <- function
( # Generates a performance report of a single model. 
  bt,                    # Assumes a single model is loaded in.
  benchmark.ret=NULL,    # Benchmark returns for CAPM analysis.
  capm.scale=252,        # Time scale for CAPM analysis. Daily = 252, monthly = 12, quarterly = 4.
  pane.width= 1300,      # Pane width in pixels
  pane.height=500,       # Pane height in pixels
  range.selector=TRUE,   # Display range selector
  zoom.buttons=TRUE      # Display zoom buttons
)
{
  colnames(benchmark.ret) <- 'benchmark'
  
  # Create peformance statistics table.
  perf.table <- performanceTable(bt)
  perf.table <- gvisCustomTable(perf.table, 
                                pane.height=50, pane.width=pane.width)
  
  # Extract model returns for manipulation.
  ret <- extractModelData(bt, target.data='ret')
  
  # Generate wealth index of model returns.
  model.index <- wealthIndex(ret)
  model.index <- log(model.index) * 100
  
  # If benchmark is loaded run value added analysis.
  if(is.xts(benchmark.ret)){
    # Construct CAPM stats table.
    capm.table <- table.CAPM(ret, benchmark.ret, scale=capm.scale, digits=4)
    capm.table <- as.data.frame(t(capm.table))
    capm.table <- cbind(rownames(capm.table), capm.table)
    rownames(capm.table) <- index(capm.table)
    colnames(capm.table)[1] <- 'model'
    capm.table <- gvisCustomTable(capm.table, pane.height=100, pane.width=pane.width)
    perf.table <- gvisMerge(perf.table, capm.table)    
    
    # Create wealth index for benchmark.
    benchmark.index <- log(wealthIndex(benchmark.ret)) * 100
    
    # Extract alpha returns and index.
    alpha <- alphaStream(ret, benchmark.ret)
    alpha.index <- log(alpha$index) * 100
    
    # Join model, benchmark and model indices.
    model.index <- cbind(model.index, benchmark.index)
    model.index <- cbind(model.index, alpha.index)
    colnames(model.index) <- spl('model,benchmark,alpha')
    
    # Join model, benchmark and model return streams.
    ret <- cbind(ret, benchmark.ret)
    ret <- cbind(ret, alpha$ret)
    colnames(ret) <- spl('model,benchmark,alpha')
  }
  
  # Scale drawdowns for proper viewing.
  dd <- Drawdowns(ret) * 100
  
  # Convert xts objects in data frames.
  dd <- xtsToDataFrame(dd)
  model.index <- xtsToDataFrame(model.index)
  
  # Construct table of model trade statistics.
  trades.stats <- as.data.frame(t(models[[1]]$trade.summary$stats))
  trades.stats <- rownamesToColumn(trades.stats, new.column.name='direction')
  
  # Construct table of model monthly returns.
  monthly.table <- monthlyReturnsTable(extractModelData(bt, target.data='equity'))
  monthly.table <- cbind(rownames(monthly.table), monthly.table)
  rownames(monthly.table) <- index(monthly.table)
  colnames(monthly.table)[1] <- 'Period'
  
  # Prepare charts for plotting.
  equity.plot <- gvisLinePlot(model.index, range.selector=range.selector, zoom.buttons=zoom.buttons, 
                               pane.height=pane.height, pane.width=pane.width)
  
  dd.plot <- gvisLinePlot(dd,range.selector=range.selector, zoom.buttons=zoom.buttons, 
                           pane.height=pane.height, pane.width=pane.width)
  
  trades.stats.table <- gvisCustomTable(trades.stats, 
                                        pane.height=100, pane.width=pane.width)

  monthly.table <- gvisCustomTable(monthly.table, 
                                   pane.height=pane.height, pane.width=pane.width)

  # Generate output.
  output <- gvisMerge(perf.table, equity.plot)
  output <- gvisMerge(output, dd.plot)
  output <- gvisMerge(output, trades.stats.table)
  output <- gvisMerge(output, monthly.table, chartid='Strategy_Report')
  return(output)
}

gvisTechnicals <- function
( # Function to create a chart of technical indicators with the Google Charts API
  xts.prices,  # 'xts.prices' parameter must be a single xts object
  length=200,
  n.std.dev=2.0, 
  scale=252, 
  direction=c('longShort', 'long', 'short'), 
  panel.options=c('full', 'main', 'returns', 'indicators')
)
{
  ###############################################################################
  # Compute technical indicators
  # Price overlay
  # Bollinger Bands
  d <- BBands(xts.prices, n=as.integer(length), sd=n.std.dev)
  d <- d[,-4]
  d <- merge(d, xts.prices)
  
  # Generate signals
  price <- xts.prices
  upper.band <- Lag(d$up)
  lower.band <- Lag(d$dn)
  mov.avg <- Lag(d$mavg)
  # Long signals
  l.signal <- ifelse(price>upper.band, 1, NA)
  l.signal <- ifelse(Lag(price)<mov.avg, 0, Lag(l.signal))
  l.signal <- na.locf(l.signal)
  # Short signals
  s.signal <- ifelse(price<lower.band, -1, NA)
  s.signal <- ifelse(Lag(price)>Lag(mov.avg), 0, Lag(s.signal))
  s.signal <- na.locf(s.signal)
  
  # Consolidate
  if(direction=='longShort') signal <- ifelse(l.signal==1, 1, ifelse(s.signal==-1, -1, 0))
  if(direction=='long') signal <- ifelse(l.signal==1, 1, 0)
  if(direction=='short') signal <- ifelse(l.signal==1, 0, ifelse(s.signal==-1, -1, 0))
  signal[is.na(signal)] <- 0
  colnames(signal) <- 'Signal'
  
  # Trades xts
  signal <- as.data.frame(signal)
  trades <- ifelse(signal==1 & Lag(signal)==0, 'Open Long', '')
  trades <- ifelse(signal==0 & Lag(signal)==1, 'Close Long', trades)
  trades <- ifelse(signal==-1 & Lag(signal)==0, 'Open Short', trades)
  trades <- ifelse(signal==0 & Lag(signal)==-1, 'Close Short', trades)
  trades[is.na(trades)] <- ''
  colnames(trades) <- 'trades'
  trades <- xts(trades, order.by=index(xts.prices))
  
  # Returns
  # Daily returns
  daily.returns <- ROC(xts.prices, n=1)
  daily.returns[is.na(daily.returns)] <- 0
  # Signal processed returns
  processed.returns <- daily.returns * xts(signal, index(xts.prices))
  # Align returns
  aligned.returns <- merge(daily.returns, processed.returns)
  colnames(aligned.returns) <- c('instrument', 'indicator')
  # Extract first date of signal returns
  date <- as.character(index(aligned.returns[aligned.returns$indicator!=0, ])[1])
  date <- paste(date, '::', sep='')
  # Subset aligned returns
  aligned.returns <- aligned.returns[date]
  
  # Instrument cummulative returns
  instrument.cummulative.r <- aligned.returns$instrument
  instrument.cummulative.r <- cumprod(1 + instrument.cummulative.r)
  instrument.cummulative.r <- instrument.cummulative.r - 1
  # Indicator overlay cummulative returns
  indicator.cummulative.r <- aligned.returns$indicator * abs(xts(signal, index(xts.prices)))
  indicator.cummulative.r <- cumprod(1 + indicator.cummulative.r)
  indicator.cummulative.r <- indicator.cummulative.r - 1
  # Consolidate
  returns <- merge(daily.returns, instrument.cummulative.r)
  returns <- merge(returns, indicator.cummulative.r)
  returns[is.na(returns)] <- 0
  colnames(returns) <- c('daily.returns', 'instrument.cummulative', 'indicator.cummulative')
  
  # Indicators
  # Rate of change and its Standard Deviation
  roc <- ROC(xts.prices, n=as.integer(length))
  roc.sd <- runSD(roc, n=as.integer(length))
  indicators <- merge(roc, roc.sd)
  colnames(indicators) <- c('ROC', 'SD')
  
  ###############################################################################
  # Data frame conversion and formatting
  # Main panel
  # Bollinger Bands overlay
  d.temp <- d
  d.temp[is.na(d.temp[, 4])] <- 0
  d.start.date <- as.character(index(d.temp[d.temp[,4]!=0,])[1])
  d.start.date <- paste(d.start.date, '::', sep='')
  d <- d[d.start.date]
  
  main.df <- as.data.frame(d)
  trades.df <- as.data.frame(trades)
  main.df$dates <- rownames(main.df)
  rownames(main.df) <- 1:nrow(main.df)
  main.df$dates <- as.Date(main.df$dates)
  
  series.count <- dim(main.df)[2]
  series.names <- colnames(main.df)
  series.names <- names(main.df)
  series.names <- series.names[-series.count]
  
  main.panel.data = reshape(main.df, 
                            idvar="Date", 
                            times=series.names, 
                            timevar="Type", 
                            varying=series.names, 
                            v.names="Value", 
                            direction="long")
  
  # Inject trade data into data frame
  # Generate trades column
  main.panel.data <- mutate(main.panel.data, trades='')
  # Prepare trades data frame
  trades.df <- as.data.frame(trades)
  trades.df$dates <- rownames(trades.df)
  rownames(trades.df) <- 1:nrow(trades.df)
  trades.df$dates <- as.Date(trades.df$dates)
  trades.df$trades <- as.character(trades.df$trades)
  trades.df[is.na(trades.df)] <- ''
  trades.df <- filter(trades.df, trades!='')
  positions.dates <- trades.df$dates
  # Find data subset we are interested in
  subset1 <- main.panel.data$dates %in% positions.dates
  subset2 <- main.panel.data$Type == names(xts.prices)
  # Perform assignement
  main.panel.data[subset1 & subset2, ]$trades <-  trades.df$trades
  
  # Signal data frame
  signal.df <- as.data.frame(signal)
  signal.df$dates <- rownames(signal.df)
  rownames(signal.df) <- 1:nrow(signal.df)
  signal.df$dates <- as.Date(signal.df$dates)
  
  series.count <- dim(signal.df)[2] - 1
  series.names <- colnames(signal.df)
  series.names <- series.names[-dim(signal.df)[2]]
  
  signal.panel.data = reshape(signal.df, 
                              idvar="Date", 
                              times=series.names, 
                              timevar="Type", 
                              varying=series.names, 
                              v.names="Value", 
                              direction="long")
  
  # Indicators  
  indicators <- indicators[d.start.date]
  indicators.df <- as.data.frame(indicators)
  indicators.df$dates <- rownames(indicators.df)
  rownames(indicators.df) <- 1:nrow(indicators.df)
  indicators.df$dates <- as.Date(indicators.df$dates)
  indicators.df[is.na(indicators.df)] <- 0
  
  series.count <- dim(indicators.df)[2] - 1
  series.names <- colnames(indicators.df)
  series.names <- series.names[-dim(indicators.df)[2]]
  
  indicators.panel.data = reshape(indicators.df, 
                                  idvar="Date", 
                                  times=series.names, 
                                  timevar="Type", 
                                  varying=series.names, 
                                  v.names="Value", 
                                  direction="long")
  
  # Returns
  returns <- returns[d.start.date]
  returns.df <- as.data.frame(returns)
  returns.df$dates <- rownames(returns.df)
  rownames(returns.df) <- 1:nrow(returns.df)
  returns.df$dates <- as.Date(returns.df$dates)
  
  series.count <- dim(returns.df)[2] - 1
  series.names <- colnames(returns.df)
  series.names <- series.names[-dim(returns.df)[2]]
  
  returns.panel.data = reshape(returns.df, 
                               idvar="Date", 
                               times=series.names, 
                               timevar="Type", 
                               varying=series.names, 
                               v.names="Value", 
                               direction="long")
  
  ###############################################################################
  # Compute summary performance statistics
  cagr.instrument <- Return.annualized(aligned.returns$instrument, scale=scale, geometric=TRUE)
  cagr.indicator <- Return.annualized(aligned.returns$indicator, scale=scale, geometric=TRUE)
  
  std.dev.instrument <- sd.annualized(aligned.returns$instrument, scale=scale)
  std.dev.indicator <- sd.annualized(aligned.returns$indicator, scale=scale)
  
  maxdd.instrument <- maxDrawdown(aligned.returns$instrument)
  maxdd.indicator <- maxDrawdown(aligned.returns$indicator)
  
  sharpe.instrument <- SharpeRatio.annualized(aligned.returns$instrument, Rf=0, scale=scale, geometric=TRUE)
  sharpe.indicator <- SharpeRatio.annualized(aligned.returns$indicator, Rf=0, scale=scale, geometric=TRUE)
  
  mar.ratio.instrument <- cagr.instrument / maxdd.instrument
  mar.ratio.indicator <- cagr.indicator / maxdd.indicator
  
  ###############################################################################
  # Convert data to a format readable by googleVis
  # Set up performance metrics table
  perf.table <- matrix(c(cagr.instrument, cagr.indicator, 
                         std.dev.instrument, std.dev.indicator, 
                         maxdd.instrument, maxdd.indicator, 
                         sharpe.instrument, sharpe.indicator, 
                         mar.ratio.instrument, mar.ratio.indicator),                      
                       nrow=dim(aligned.returns)[2], ncol=5)
  
  perf.table <- as.data.frame(perf.table)
  perf.table <- cbind(perf.table, colnames(aligned.returns))
  perf.table.columns <- dim(perf.table)[2]
  perf.table.rows <- dim(perf.table)[1]
  perf.table <- perf.table[, c(perf.table.columns, 1:perf.table.columns-1)]
  rownames(perf.table) <- 1:perf.table.rows
  colnames(perf.table) <- c('Series', 'CAGR', 'Std. Dev', 'Max DD', 'Sharpe', 'MAR Ratio')
  
  ##############################################################################
  # Graphical output preparation
  # Construct panels
  # Bollinger Bands
  main.panel <- gvisAnnotatedTimeLine(main.panel.data, 
                                      datevar="dates", numvar="Value", idvar="Type", titlevar='trades', 
                                      options=list(
                                        colors="['gray', 'black', 'gray', 'blue']", 
                                        displayAnnotations=TRUE, 
                                        width=1290, height=400, 
                                        scaleType='maximized', 
                                        displayRangeSelector=FALSE, 
                                        displayZoomButtons=TRUE))
  
  # Signal panel
  signal.panel <- gvisAnnotatedTimeLine(signal.panel.data, 
                                        datevar="dates", numvar="Value", idvar="Type", 
                                        options=list(
                                          colors="['blue']", 
                                          width=1300, height=200, 
                                          scaleType='maximized', 
                                          displayRangeSelector=FALSE))  
  # Returns
  returns.panel <- gvisAnnotatedTimeLine(returns.panel.data, 
                                         datevar="dates", numvar="Value", idvar="Type", 
                                         options=list(
                                           colors="['gray', 'blue', 'black']", 
                                           width=960, height=200, 
                                           scaleType='maximized', 
                                           displayRangeSelector=FALSE, 
                                           displayZoomButtons=TRUE))
  
  perf.table.plot <- gvisTable(perf.table, 
                               options=list(
                                 width=360, height=200), 
                               formats=list('CAGR'='#.##%', 
                                            'Std. Dev'='#.##%', 
                                            'Max DD'='#.##%', 
                                            'Sharpe'='#.##', 
                                            'MAR Ratio'='#.##'))
  
  returns.panel <- gvisMerge(returns.panel, perf.table.plot, horizontal=TRUE)
  
  # Indicators
  indicators.panel <- gvisAnnotatedTimeLine(indicators.panel.data, 
                                            datevar="dates", numvar="Value", idvar="Type", 
                                            options=list(
                                              colors="['blue', 'black', 'gray']", 
                                              width=960, height=200, 
                                              scaleType='maximized', 
                                              displayRangeSelector=FALSE, 
                                              displayZoomButtons=TRUE))
  
  ##############################################################################
  # Display options
  if(panel.options=='full'){
    final.panel <- gvisMerge(main.panel, returns.panel, chartid='Technicals')
    final.panel <- gvisMerge(final.panel, indicators.panel, chartid='Technicals')
  }else{
    if(panel.options=='returns'){
      final.panel <- gvisMerge(main.panel, returns.panel, chartid='Technicals')
    }else{
      if(panel.options=='indicators'){
        final.panel <- gvisMerge(main.panel, indicators.panel, chartid='Technicals')
      }else{
        final.panel <- main.panel
      }
    }
  }
  
  ##############################################################################
  # Final result
  plot(final.panel)
}

multiplot <- function
################################
# Multiple plot function 
# ggplot objects can be passed in ..., or to plotlist (as a list of ggplot objects)
# - cols:   Number of columns in layout
# - layout: A matrix specifying the layout. If present, 'cols' is ignored.
#
# If the layout is something like matrix(c(1,2,3,3), nrow=2, byrow=TRUE),
# then plot 1 will go in the upper left, 2 will go in the upper right, and
# 3 will go all the way across the bottom.
#
( ..., 
 plotlist=NULL, 
 file, 
 cols=1, 
 layout=NULL) 
{
  require(grid)
  
  # Make a list from the ... arguments and plotlist
  plots <- c(list(...), plotlist)
  
  numPlots = length(plots)
  
  # If layout is NULL, then use 'cols' to determine layout
  if (is.null(layout)) {
    # Make the panel
    # ncol: Number of columns of plots
    # nrow: Number of rows needed, calculated from # of cols
    layout <- matrix(seq(1, cols * ceiling(numPlots/cols)),
                     ncol = cols, nrow = ceiling(numPlots/cols))
  }
  
  if (numPlots==1) {
    print(plots[[1]])
    
  } else {
    # Set up the page
    grid.newpage()
    pushViewport(viewport(layout = grid.layout(nrow(layout), ncol(layout))))
    
    # Make each plot, in the correct location
    for (i in 1:numPlots) {
      # Get the i,j matrix positions of the regions that contain this subplot
      matchidx <- as.data.frame(which(layout == i, arr.ind = TRUE))
      
      print(plots[[i]], vp = viewport(layout.pos.row = matchidx$row,
                                      layout.pos.col = matchidx$col))
    }
  }
}