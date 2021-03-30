########################################################
# R script used in the data processing and analysis of #
# Human Movement Pattern manuscript;        2021/03/30 #
########################################################

###############
### Content ###
###############

# R packages used
# Data processing
# - Folder structure
# - Data cleaning
# - Merging the files
# Data analysis
# - Identifying the sleeping locations
# - Estimating home coordinates
# - Measuring maximum daily Euclidian distance (MDED) away from home (Fig 1)
# - Multi-day trips
# - Days spent in different places (Fig 2)
# - Space utilization estimated with biased-random bridges (BRB) (Fig 3)
# - Nights spent in different places (Fig 4)
# - Consecutive nights spent in different places (Fig 5)
# - Mixed-effects model (Table 2)

########################
### R packages used ####
########################

require(adehabitatHR)
library(cowplot) #cowplot makes ggplot2 default theme_gray() disappear
library(dplyr)
library(ggbeeswarm) #for beeswarm plot
library(ggplot2)
library(ggpubr)
library(lme4) #for linear mixed effect model
library(lubridate) #for date & time formatting
library(magrittr)
library(MASS) #for glm.nb
library(plyr)
library(plotly)
library(proj4)
library(raster)
library(rasterVis)
library(reshape2)
library(rgdal) #for reading gpkg (geopackage files) for farms and forests that are made in qGis
library(rgeos) #for gDistance
library(scales)
library(sp) #for spatial* data structures
library(sjPlot) #for getting result table of mixed effect model
library(viridis)




#########################
### Data processing #####
#########################

### - Folder structure ####

# The folder structure of the working directory (wd) could be represented as follows:
# .
# +-- raw_data
# |   +-- recruitmentPlaceA
# |   |   +-- villageX
# |   |   |    +-- person1
# |   |   |    |    +-- gpsData1.csv
# |   |   |    |    +-- gpsData2.csv
# |   |   |    +-- person2
# |   |   +-- villageY
# |   +-- recruitmentPlaceB
# |   |   +-- villageZ
# |   |   |    +-- person49
# |   |   |    +-- person50
# +-- output
# |   +-- processed_data
# |   +-- figures

# Each person in the raw_data folder has multiple gpsData*.csv files. Not all folders and files are shown. 

#---------------------------------------------------------------------------------------------------

### - Data cleaning ####

for(i in 1:length(fileNames)){
  toClean <- read.csv(paste0("wd/raw_data/recruitmentPlace*/person*",fileNames[i])) #read in

  # Consistent date format
  toClean$Date <- dmy(toClean$Date) #change date format
  toClean$Date <- gsub("-","/",toClean$Date) #replace dash with slash

  # Combine data and time columns into dt
  toClean$dt <- as.POSIXct(paste(toClean$Date, toClean$Time), format = "%Y/%m/%d %H:%M:%S", tz="Asia/Bangkok")

  # Remove duplicated records within each person
  toClean <- toClean[(!duplicated(toClean$dt)),]

  # Remove records with invalid dates (study begins in March 2017)
  toClean <- [(toClean$dt>as.POSIXct("2017/03/01 00:00:00", format = "%Y/%m/%d %H:%M:%S", tz="Asia/Bangkok", origin="1970-01-01 00:00.00 UTC")),]

  write.csv(toClean,paste0("output/processed_data",fileNames[i]),row.names = FALSE)
}

#---------------------------------------------------------------------------------------------------

### - Merging the files ####

# CSV files for each person is merged using the following function, called with relevant parameters:

CSV_Merger <- function(folderPath, recruitment="", village="", individual=""){
  
  setwd(folderPath)

  #read files
  #extract list of CSV files within the folder
  fileNames <- list.files()[grep("*.csv",list.files())]
  
  fileContents <- list() #initiate list to store files
  
  fileContents <- lapply(fileNames,read.csv) #read files
  
  #add column for original file name
  for(i in 1:length(fileContents)){
    fileContents[[i]]$Origin <- rep(fileNames[i],times=nrow(fileContents[[i]]))
  }
  
  #checking
  validFiles <- rep(TRUE,length(fileNames))
  #1. dimension
  dimCheck <- lapply(fileContents,dim) 
  dimCheckResults <- matrix(unlist(dimCheck),2,length(fileNames))
  #2. variable names
  varValidNames <- c("Date","Time","Latitude","Longitude","Altitude","Speed", "Course","Type","Distance","Essential","Origin")
  varNameCheck <- lapply(fileContents,colnames)
  varNameCheckResults <- sapply(varNameCheck,function(x) (varValidNames %in% x)) #to print
  validFiles <- validFiles*(apply(varNameCheckResults,2,all)) #merge only these valid files
  
  checkResults <- as.data.frame(t(rbind(dimCheckResults,varNameCheckResults))) 
  colnames(checkResults) <- c("Row", "Col", varValidNames)
  rownames(checkResults) <- fileNames
  
  #anonymizied code
  fileID <- paste0(recruitment,village,individual)
  
  #merging
  output <- do.call("rbind", fileContents[validFiles==1])
  if(fileID!=""){
    output <- cbind(output,rep(fileID,nrow(output)))
    names(output)[ncol(output)] <- "fileID"
  }
  if(sum(dimCheckResults[1,validFiles==1])==nrow(output)){
    write.csv(output, paste0(fileID,"_merged_",sum(validFiles),"__",gsub(":|-","",Sys.time()),".csv"))
  }
  write.csv(checkResults, paste0(fileID,"_checkResults_",gsub(":|-","",Sys.time()),".csv"))
}

#---------------------------------------------------------------------------------------------------



######################
### Data analysis ####
######################

### - Identifying the sleeping locations ####

# All merged CSV files (one for each person) are read into a "list" data structure
allPersonsList <- lapply(mergedCSVfiles, read.csv)
# where "mergedCSVfiles" is a list of file names of the merged CSV files

# Extract "hour" only portion of "dt"
allPersonsList <- lapply(allPersonsList, function(x){
    cbind(x, ho=x$dt$hour)
})

# The last GPS point of the day between 6pm to 12 midnight was considered to be the location where an individual spent the night. 
sleepLocation <- lapply(allPersonList, function(x){
  x[which(x$ho>=18),]
})

#---------------------------------------------------------------------------------------------------

### - Estimating home coordinates ####

# The median center of sleeping points of a person(calculated previously) was assumed to be the individual’s home location. Calculation was done and verified in ArcMap software. Coordinates of the houses are stored as "houses_points.csv".

hp <- read.csv("houses_points.csv")
names(hp)[1] <- "id"
coordinates(hp) <- c("XCoord", "YCoord")
proj4string(hp) <- CRS("+proj=longlat +datum=WGS84") 

w= 266 #width in meters to use as buffer

bList_longlat <- list() #initiate list to store results

for(i in 1:length(hp)){
bList_longlat[[i]] <- buffer(subset(hp, hp$id==i),width=w)
}

joined <- do.call(bind, bList_longlat) #merge the list
housesWithBuffer <- SpatialPolygonsDataFrame(joined, as.data.frame(hp)) #transform into SPDF

#Save SPDF as ESRI shape file for checking and for calculations in later sections
writeOGR(housesWithBuffer,dsn="output/Places of Special Interest",layer="housesWithBuffer", driver="ESRI Shapefile")

#Transform SPDF into rasters & save as tiff file, in order to perform raster calculations (utilization of home) 
for(i in 1:length(housesWithBuffer)){
    writeRaster(rasterize(subset(housesWithBuffer,housesWithBuffer$id==i),myanmarForest,field="fileID"), paste0("output/houses/",housesWithBuffer$fileID[i],".tif"))
}

#---------------------------------------------------------------------------------------------------

### - Measuring maximum daily Euclidian distance (MDED) away from home (Fig 1) ####

# Merge all persons' data into single file
allPoints <- do.call("rbind", allPersonsList)

coordinates(hp) <- ~XCoord + YCoord
coordinates(allPoints) <- ~Longitude+Latitude

# Transform into projected coordinate systems for distance calculation
#setting correct coordinate system of the original data points
proj4string(hp) <- CRS("+proj=longlat +datum=WGS84") 
proj4string(allPoints) <- CRS("+proj=longlat +datum=WGS84") 
#template to project
newProj <- CRS("+proj=utm +zone=47N +ellps=WGS84 +units=m")
hp <- spTransform(hp, newProj)
allPoints <- spTransform(allPoints, newProj)

#fileID for each person to iterate over
fileIDindex <- unique(allPoints$fileID)

distFromHomeList <- list()
for(i in 1:length(fileIDindex)){
  tmp <- allPoints[allPoints$fileID==fileIDindex[i],] 
  
  # Calculate geometric distance of all points of each person from his/her respective home
  tmp$metersFromHouse <- gDistance(hp[hp$fileID==fileIDindex[i],],tmp, byid=TRUE)[,1]
  
  # Generate maximum distance from home for each day in each person (summary function generates this max value)
  distFromHomeList[[i]] <- as.data.frame(do.call(rbind, by(tmp$metersFromHouse,tmp$Date,summary)))
  
  rm(tmp)
}

distFromHome <- do.call(rbind, distFromHomeList)

# Age group, and gender are added to "distFromHome" data before the next step. 

# Generate figure 1, which includes 
# Wilcoxon rank-sum test to compare the distributions of MDED
gDN2<-ggplot(distFromHome,aes(x=ageGp,y=Max.))+geom_violin(aes(fill = ageGp))+
  geom_boxplot(width=0.1)+theme_minimal()+
  scale_y_log10(breaks = c(1e+01, 1e+02, 1e+03, 1e+04, 1e+05), labels = c("0.01", "0.1", "1", "10", "100"))+
  scale_fill_manual(values=ageShapeVal)
my_comparisons <- list( c("<20", "20-40"), c("<20", ">=40"), c("20-40", ">=40") )
gDN2+stat_compare_means(method = "wilcox.test",comparisons = my_comparisons, label =  "p.signif", label.x = 1.5) # Add pairwise comparisons p-value

#---------------------------------------------------------------------------------------------------

### - Multi-day trips ####

#threshold for being away from home: min distance > 266 meters
distFromHomeAway <- lapply(distFromHome,function(x) {cbind(x,(x$Min.>266))}) 
distFromHomeAway <- lapply(distFromHomeAway, function(x) {
  colnames(x)[ncol(x)] <- "Away" #rename the column
  x
})

#count the no. of consecutive days away
for(j in 1:length(distFromHomeAway)){
  distFromHomeAway[[j]]$ConsecutiveAway <- NA
  for(i in 1:nrow(distFromHomeAway[[j]])){
    if(i==1){
      if(distFromHomeAway[[j]]$Away[i]) {
        distFromHomeAway[[j]]$ConsecutiveAway[i] <- 1
      } else {distFromHomeAway[[j]]$ConsecutiveAway[i] <- 0}
    } else{
      if(distFromHomeAway[[j]]$Away[i-1] & distFromHomeAway[[j]]$Away[i]){
        distFromHomeAway[[j]]$ConsecutiveAway[i] <- distFromHomeAway[[j]]$ConsecutiveAway[i-1] + 1
      }
      if(!distFromHomeAway[[j]]$Away[i-1] & distFromHomeAway[[j]]$Away[i]){
        distFromHomeAway[[j]]$ConsecutiveAway[i] <- 1
      } 
      if(!distFromHomeAway[[j]]$Away[i]) {distFromHomeAway[[j]]$ConsecutiveAway[i] <- 0 }
    }
  }
}

#identify the total no. of days for each multi-day trip
for(j in 1:length(distFromHomeAway)){
  distFromHomeAway[[j]]$EachAway <- NA
  hiAway <- 0
  for(i in nrow(distFromHomeAway[[j]]):1){
    if(distFromHomeAway[[j]]$ConsecutiveAway[i]==0){
      hiAway <- 0
      distFromHomeAway[[j]]$EachAway[i] <- 0
      next
    } else {
      if(hiAway<distFromHomeAway[[j]]$ConsecutiveAway[i]){
        hiAway <- distFromHomeAway[[j]]$ConsecutiveAway[i]
      }
    }
    distFromHomeAway[[j]]$EachAway[i] <- hiAway
  }
}

#summarize multi-day trips for each individual
consecDaysAwayL <- lapply(distFromHomeAway, function(x){
  table(rle(x$EachAway)$values)
})
consecDaysAwayL

#---------------------------------------------------------------------------------------------------

### - Days spent in different places (Fig 2) ####

allPoints <- do.call("rbind", allPersonsList) 
allPoints$newDate <- as.Date(allPoints$dt) #create new date/time variable 
coordinates(singleFile) <- ~Longitude+Latitude
proj4string(singleFile) <- CRS("+proj=longlat +datum=WGS84")

#read in relevant shape files and project to same coordinate system
housesBuffer <- readOGR(dsn="Places of Special Interest/housesWithBuffer.shp",layer="housesWithBuffer")
housesBuffer <- spTransform(housesBuffer, CRS(proj4string(allPoints)))
forests <- readOGR(dsn="Places of Special Interest/onlyForests.shp",layer="onlyForests") #identified manually through GoogleEarth
forests <- spTransform(forests, CRS(proj4string(allPoints)))
farms <- readOGR(dsn="Places of Special Interest/onlyFarms.shp",layer="onlyFarms") #identified manually through GoogleEarth
farms <- spTransform(farms, CRS(proj4string(allPoints)))

results <- data.frame(matrix(NA, nrow=length(fileIDindex), ncol=5))

#count number of GPS records inside the corresponding polygons (home, farms, forests)
for(i in 1:length(fileIDindex)){
  visitedPlace <- allPoints[allPoints$fileID==fileIDindex[i],]
  homePlace <- housesBuffer[housesBuffer$fileID==fileIDindex[i],]
  visitedHome <- visitedPlace[homePlace,] #spatial subset is done here!!!
  daysvisitedHome <- length(which(table(visitedHome$newDate)>2)) #presence of 2 GPS points constitutes being at that place
  
  visitedForests <- visitedPlace[forests,]
  daysvisitedForests <- length(which(table(visitedForests$newDate)>2))
  
  visitedFarms <- visitedPlace[farms,]
  daysvisitedFarms <- length(which(table(visitedFarms$newDate)>2))
  
  daysParticipated <- length(unique(allPoints[allPoints$fileID==fileIDindex[i],]$newDate)) #denominator
  
  results[i,] <- cbind(fileIDindex[i], daysParticipated, daysvisitedHome, daysvisitedFarms, daysvisitedForests)
}
names(results) <- c("fileID", "daysParticipated","daysAtHome", "daysVisitedFarms", "daysVisitedForests")

#merge with demographic data
# demoData <- load demographic data here!
visits <- merge(demoData, results, by.y="fileID", by.x="pid")
#calculate proportions
visits$Home <- visits$daysAtHome/visits$daysParticipated
visits$Farms <- visits$daysVisitedFarms/visits$daysParticipated
visits$Forests <- visits$daysVisitedForests/visits$daysParticipated
visitsM <- melt(visits, id.vars=c("pid","Sex","ageGp"), measure.vars = c("Farms","Forests","Home"))

#Fig 2
png(filename = paste0("output/figures/Fig2_visitsByAge.png"), width = 1300, height = 1000)
visitsByAge <- ggplot(visitsM,aes(x=variable,y=value))+
  geom_boxplot(outlier.size=4, lwd=1.3, fatten=1)+
  facet_grid(.~ageGp)+
  stat_summary(fun.y=mean, geom="point", shape=20, size=14) +
  xlab("")+
  ylab("Space Utilization")+
  theme_bw(base_size = 35) 
visitsByAge
dev.off()


#---------------------------------------------------------------------------------------------------

### - Space utilization estimated with biased-random bridges (BRB) (Fig 3) ####

d <- do.call("rbind", allPersonsList) #combine all files
dt <- d$dt

## Separate coordinates, and make projections
coord <- data.frame(d$Longitude, d$Latitude)
coord <- data.frame(project(coord, "+proj=utm +zone=47 +ellps=WGS84 +datum=WGS84 +units=m +no_defs")) #change to projected system
idn <- d$fileID

## Create ltraj separating data by individual and trip
# Type II for time recorded track
d2 <- as.ltraj(coord, dt, id=idn, typeII = TRUE)
summary(d2)
#saveing big, all combined ltraj file as RDS
#saveRDS(d2,file = "output/large_d.RDS")

#filling up with NA in between
refda <- strptime("2017/03/26 00:00:00", "%Y/%m/%d %H:%M:%S", tz="Asia/Bangkok")
d3 <- setNA(d2, refda, 30, units = "min") 

#rounding time coordinates
d4 <- sett0(d3, refda, 30, units = "min") 
#saveRDS(d4,file = "output/large_d4.RDS")

# Estimate the diffusion component
# create a grid
forestClassProj <- raster("output/Myanmar_Forest_Class_Projected.tif")
ext <- extent(forestClassProj)
r <- raster(ext, res=c(26.7, 27.7))
p <- as(r, "SpatialPixels")

# UD estimation for each person
# plotting of UD and saving them as dataframe (RDS), and rasters (tif)
for(i in 1:length(d4)){

  diffusion <- BRB.D(d4[i], Tmax = tmax, Lmin = lmin, habitat= NULL, activity = NULL)
  ud1 <- BRB(d4[i], D=diffusion, Tmax = tmax, Lmin=lmin, hmin=hmin, type = "UD",
             b = FALSE, same4all = FALSE, extent = 0.1, grid= p)
  #summary(ud1)
  
  # Plot utilisation distribution
  vud1 <- getvolumeUD(ud1)
  png(filename = paste0("output/UD/UD_",summary(d4)$burst[i],".png"), width = 1800, height = 1000)
  image(vud1)
  dev.off()
  
  saveRDS(ud1, file = paste0("output/UD/ud_",summary(d4)$burst[i],"_",gsub(":|-","",Sys.time()),".RDS"))
  
  writeRaster(raster(ud1),paste0("output/UD/ud_",summary(d4)$burst[i],"_",".tif"))
}

# Load rasters for Farms and Forests
farms <- raster("Places of Special Interest/rFarms.tif")
forests <- raster("Places of Special Interest/rForests.tif")
projFarms <- projectRaster(from=farms,res=c(27.7,27.7), crs = "+proj=utm +zone=47 +ellps=WGS84 +datum=WGS84 +units=m +no_defs", method = "ngb")
projForests <- projectRaster(from=forests,res=c(27.7,27.7), crs = "+proj=utm +zone=47 +ellps=WGS84 +datum=WGS84 +units=m +no_defs", method = "ngb")
mFarms <- as.matrix(projFarms[[1]])
mForests <- as.matrix(projForests[[1]])

# File path to UD
filePath <- "output/UD/"
fileNames <- list.files(filePath)

# Create a dataframe to store results
colNamesResult <- c("id", "timeOfDay","season", "Farms", "Forests","Own House")
result <- data.frame(matrix(NA,length(fileNames),3))

for(i in 1:length(fileNames)){
  
  udRaster <- raster(paste0(filePath,fileNames[i]))
  proj4string(udRaster) <- CRS("+proj=utm +zone=47N ellps=WGS84")
  udRasterCropped <- crop(udRaster, projFarms) #ud1Raster has greater extent
  udM <- as.matrix(udRasterCropped[[1]])
  
  if(!all(dim(mFarms)==dim(udM))){
    print(paste("Problem in",i))
    break
  }
  
  # Load raster for each person [i]
  housePath <- paste0("Places of Special Interest/houses/",strsplit(fileNames[i],"_")[[1]][2],".tif")
  isOwnHouse <- as.numeric(strsplit(fileNames[i],"_")[[1]][2]) #to test if the raster pixel is his/her house
  
  house <- raster(housePath)
  mHouse <- as.matrix(projectRaster(from=house,res=c(27.7,27.7), crs = "+proj=utm +zone=47 +ellps=WGS84 +datum=WGS84 +units=m +no_defs", method = "ngb")[[1]])
  
  # Calculate the UD values in each grid corresponding to each place in the respective rasters
  result[i,1] <- sum(udM[which(mFarms==10000, arr.ind=TRUE)]*27.7^2)
  result[i,2] <- sum(udM[which(mForests==20000, arr.ind=TRUE)]*27.7^2)
  result[i,3] <- sum(udM[which(mHouse==isOwnHouse, arr.ind=TRUE)]*27.7^2)
  
  rm(udM,udRaster, udRasterCropped, house, mHouse) #remove files in the memory
}


idCol <- sapply(fileNames, function(x){strsplit(x,"_")[[1]][2]})
timeOfDayCol <- rep("all",length(fileNames))
seasonCol <- rep("all",length(fileNames))
result <- cbind(idCol,timeOfDayCol,seasonCol,result)
colnames(result) <- colNamesResult

saveRDS(result,"output/UD_allResult.RDS")

# 3D UD graph in Fig 3 is generated as follows:

ud <- readRDS("output/UD/ud_*.RDS") #read one UD file

# Extract UD for all data
all <- getvolumeUD(ud)

# Convert to data frame
all.d <- as.data.frame(all)

# Reorder data frame variables
all.x <- data.frame(all.d$Var2, all.d$Var1, all.d$n)

# Rename variables
names(all.x)<- c("X", "Y", "UD")

# Assign 1 to grid square where UD < 99
all.x$include1[all.x$UD < 99] <- 1

# Remove grid where UD > 99
all.x <- na.omit(all.x)

# Scale to total probabilities
all.x$UD <- 100 - all.x$UD

# Minutes spent per area
all.m <- all.x
tot <- sum(all.m$UD)
all.m$UD <- all.m$UD/tot


# Create surface plot
# Coerce to matrix
a <- acast(all.x, Y~X, value.var="UD")

# Plot data
plot_ly(z=a, type = "surface")

# Colours
cols <- brewer.pal(9, "Purples")
cols <- colorRampPalette(cols)

# UD 3D example 
p <- plot_ly(z = a, type = "surface", showscale=TRUE, colors = (plasma(100))) %>% 
  layout(title = " ",
         scene = list(
           xaxis = list(title = "X", showticklabels=FALSE), 
           yaxis = list(title = "Y", showticklabels=FALSE), 
           zaxis = list(title = "Utilisation Probability")))
p

widget_file_size <- function(p) {
  d <- "output/UD3D"
  withr::with_dir(d, htmlwidgets::saveWidget(p, "index.html"))
  f <- file.path(d, "index.html")
  mb <- round(file.info(f)$size / 1e6, 3)
  message("File is: ", mb," MB")
}

#write html 3D file
widget_file_size(p)

#---------------------------------------------------------------------------------------------------

### - Nights spent in different places (Fig 4) ####

# Load sleeping locations
slept <- do.call(rbind, sleepLocation)
slept$Date <- as.Date(slept$dt)
coordinates(slept) <- ~Longitude+Latitude
proj4string(slept) <- CRS("+proj=longlat +datum=WGS84")

# Load polygons for home, forests and farms
housesBuffer <- readOGR(dsn="Places of Special Interest/housesWithBuffer.shp",layer="housesWithBuffer")
housesBuffer <- spTransform(housesBuffer, CRS(proj4string(slept)))
forests <- readOGR(dsn="Places of Special Interest/onlyForests.shp",layer="onlyForests")
forests <- spTransform(forests, CRS(proj4string(slept)))
farms <- readOGR(dsn="Places of Special Interest/onlyFarms.shp",layer="onlyFarms")
farms <- spTransform(farms, CRS(proj4string(slept)))

fileIDindex <- unique(slept$fileID) 
results <- data.frame(matrix(NA, nrow=length(fileIDindex), ncol=5))

for(i in 1:length(fileIDindex)){
  sleptPlace <- slept[slept$fileID==fileIDindex[i],]
  homePlace <- housesBuffer[housesBuffer$fileID==fileIDindex[i],]
  sleptHome <- sleptPlace[homePlace,] #spatial subset is done here!!!
  daysSleptHome <- nrow(sleptHome)
  daysSleptForest <- nrow(sleptPlace[forests,])
  daysSleptFarm <- nrow(sleptPlace[farms,])
  daysParticipated <- length(slept[slept$fileID==fileIDindex[i],]) #denominator
  
  results[i,] <- cbind(fileIDindex[i], daysParticipated, daysSleptHome, daysSleptFarm, daysSleptForest)
}

names(results) <- c("fileID", "daysParticipated","daysSleptHome", "daysSleptFarm", "daysSleptForest")
results$notSleptHome <- results$daysParticipated-results$daysSleptHome

# Merge with demographic data
dSlept <- merge(demoData, results, by.y="fileID", by.x="pid")

# Melt data to have no. of days slept in farm and forests for different gender and age groups
dSleptM <- melt(dSlept, id.vars = c("pid","Sex","ageGp"), measure.vars = c("daysSleptFarm", "daysSleptForest"))

# Filter only records with more than 1 night
dSleptM1 <- dSleptM[dSleptM$value>0,] 

# Fig 4
png(filename = "output/figures/Fig4.png", width = 1200, height=1000, units="px")
gB2 <- ggplot(dSleptM1, aes(x=variable, y=value))+
  geom_boxplot(outlier.alpha=0, color=alpha("black",0.9), alpha=0.3)+
  geom_beeswarm(cex=3.3, size=15, aes(shape=factor(Sex, levels=c("M","F")), col=factor(ageGp,levels=c("<20","20-40",">=40"))))+
  scale_shape_manual(name="Gender", values=sexColVal)+
  scale_color_manual(name="Age group", values=ageShapeVal)+
  scale_y_continuous(name="Total number of nights slept", breaks=c(1,25,50,75,100,125))+
  scale_x_discrete(name="",labels=c("Farm", "Forest"))+
  theme_bw(base_size = 35)
gB2
dev.off()

#---------------------------------------------------------------------------------------------------

### - Consecutive nights spent in different places (Fig 5) ####

sleptForests <- sleptFarms <- list()

for(i in 1:length(fileIDindex)){
  sleptPlace <- slept[slept$fileID==fileIDindex[i],]
  
  sleptForests[i] <- sleptPlace[forests,]
  sleptFarms[i] <- sleptPlace[farms,]
  
}

#total nights spent
sleptForestsTotal <- sapply(sleptForests, length)
sleptFarmsTotal <- sapply(sleptFarms, length)

#discard those who didn't sleep at farms/forests at all
sleptForests <- sleptForests[sleptForestsTotal>0]
sleptFarms <- sleptFarms[sleptFarmsTotal>0]

# find consecutive nights, sleptForests
for(j in 1:length(sleptForests)){
  sleptForests[[j]]$ConsecutiveAway <- NA
  for(i in 1:nrow(sleptForests[[j]])){
    if(i==1){
      sleptForests[[j]]$ConsecutiveAway[i] <- 0
    } else{
      if(sleptForests[[j]]$Date[i-1] == sleptForests[[j]]$Date[i]-1){
        sleptForests[[j]]$ConsecutiveAway[i] <- sleptForests[[j]]$ConsecutiveAway[i-1] + 1
      } else{sleptForests[[j]]$ConsecutiveAway[i] <- 0}
    }
  }
}


for(j in 1:length(sleptForests)){
  sleptForests[[j]]$EachAway <- NA
  hiAway <- 0
  for(i in nrow(sleptForests[[j]]):1){
    if(sleptForests[[j]]$ConsecutiveAway[i]==0){
      sleptForests[[j]]$EachAway[i] <- hiAway
      hiAway <- 0
      next
    } else {
      if(hiAway<sleptForests[[j]]$ConsecutiveAway[i]){
        hiAway <- sleptForests[[j]]$ConsecutiveAway[i]
      }
    }
    sleptForests[[j]]$EachAway[i] <- hiAway
  }
}

# Summarize no. of days slept in the forests for each person
sleptForestsAwayL <- lapply(sleptForests, function(x){
  table(rle(x$EachAway)$values)
})


sleptForestsAway <- lapply(sleptForestsAwayL, as.data.frame)
for(i in 1:length(sleptForestsAway)){
  sleptForestsAway[[i]]$fileID <- rep(sleptForests[[i]]$fileID[1], nrow(sleptForestsAway[[i]]))
}

# Link with age group and gender 
sleptForestsAwayM <- do.call(rbind.fill, sleptForestsAway)
sleptForestsAwayM$Sex <- NA
sleptForestsAwayM$ageGp <- NA

for(i in 1:nrow(sleptForestsAwayM)){
  if(length(which(demoData$pid==sleptForestsAwayM$fileID[i]))){
    sleptForestsAwayM$Sex[i] <- as.character(demoData[which(demoData$pid==sleptForestsAwayM$fileID[i]),]$Sex)
    sleptForestsAwayM$ageGp[i] <- as.character(demoData[which(demoData$pid==sleptForestsAwayM$fileID[i]),]$ageGp)
  }
}
sleptForestsAwayM <- sleptForestsAwayM[!(is.na(sleptForestsAwayM$Sex)),] #remove records without demographi data
sleptForestsAwayM$Var1 <- as.numeric(sleptForestsAwayM$Var1)
sleptForestsAwayM <- sleptForestsAwayM[sleptForestsAwayM$Var1>=2,]

#
daysAwayLab <- c("2-5", "6-10", "11-15", "16-20", ">20")
sleptForestsAwayM$ConsecutiveDaysAway <- cut(sleptForestsAwayM$Var1, breaks=c(2,6,11,16,21,100), right=FALSE, labels=daysAwayLab)
#recalculate the Freq based on new categorization
sleptForestsAwayM$Frequency <- NA
for(i in 1:nrow(sleptForestsAwayM)){
  tmpIndex <- which((sleptForestsAwayM$fileID == sleptForestsAwayM$fileID[i]) & (sleptForestsAwayM$ConsecutiveDaysAway == sleptForestsAwayM$ConsecutiveDaysAway[i]))
  sleptForestsAwayM$Frequency[i] <- sum(sleptForestsAwayM$Freq[tmpIndex])
}

##END Forests####

# find consecutive nights, sleptFarms
for(j in 1:length(sleptFarms)){
  sleptFarms[[j]]$ConsecutiveAway <- NA
  for(i in 1:nrow(sleptFarms[[j]])){
    if(i==1){
      sleptFarms[[j]]$ConsecutiveAway[i] <- 0
    } else{
      if(sleptFarms[[j]]$Date[i-1] == sleptFarms[[j]]$Date[i]-1){
        sleptFarms[[j]]$ConsecutiveAway[i] <- sleptFarms[[j]]$ConsecutiveAway[i-1] + 1
      } else{sleptFarms[[j]]$ConsecutiveAway[i] <- 0}
    }
  }
}


for(j in 1:length(sleptFarms)){
  sleptFarms[[j]]$EachAway <- NA
  hiAway <- 0
  for(i in nrow(sleptFarms[[j]]):1){
    if(sleptFarms[[j]]$ConsecutiveAway[i]==0){
      sleptFarms[[j]]$EachAway[i] <- hiAway
      hiAway <- 0
      next
    } else {
      if(hiAway<sleptFarms[[j]]$ConsecutiveAway[i]){
        hiAway <- sleptFarms[[j]]$ConsecutiveAway[i]
      }
    }
    sleptFarms[[j]]$EachAway[i] <- hiAway
  }
}

# Summarize no. of days slept in the farms for each person
sleptFarmsAwayL <- lapply(sleptFarms, function(x){
  table(rle(x$EachAway)$values)
})


sleptFarmsAway <- lapply(sleptFarmsAwayL, as.data.frame)
for(i in 1:length(sleptFarmsAway)){
  sleptFarmsAway[[i]]$fileID <- rep(sleptFarms[[i]]$fileID[1], nrow(sleptFarmsAway[[i]]))
}

# Link with age group and gender 
sleptFarmsAwayM <- do.call(rbind.fill, sleptFarmsAway)
sleptFarmsAwayM$Sex <- NA
sleptFarmsAwayM$ageGp <- NA

for(i in 1:nrow(sleptFarmsAwayM)){
  if(length(which(demoData$pid==sleptFarmsAwayM$fileID[i]))){
    sleptFarmsAwayM$Sex[i] <- as.character(demoData[which(demoData$pid==sleptFarmsAwayM$fileID[i]),]$Sex)
    sleptFarmsAwayM$ageGp[i] <- as.character(demoData[which(demoData$pid==sleptFarmsAwayM$fileID[i]),]$ageGp)
  }
}
sleptFarmsAwayM <- sleptFarmsAwayM[!(is.na(sleptFarmsAwayM$Sex)),] #remove records without demographi data
sleptFarmsAwayM$Var1 <- as.numeric(sleptFarmsAwayM$Var1)
sleptFarmsAwayM <- sleptFarmsAwayM[sleptFarmsAwayM$Var1>=2,]

#
daysAwayLab <- c("2-5", "6-10", "11-15", "16-20", ">20")
sleptFarmsAwayM$ConsecutiveDaysAway <- cut(sleptFarmsAwayM$Var1, breaks=c(2,6,11,16,21,100), right=FALSE, labels=daysAwayLab)
#recalculate the Freq based on new categorization
sleptFarmsAwayM$Frequency <- NA
for(i in 1:nrow(sleptFarmsAwayM)){
  tmpIndex <- which((sleptFarmsAwayM$fileID == sleptFarmsAwayM$fileID[i]) & (sleptFarmsAwayM$ConsecutiveDaysAway == sleptFarmsAwayM$ConsecutiveDaysAway[i]))
  sleptFarmsAwayM$Frequency[i] <- sum(sleptFarmsAwayM$Freq[tmpIndex])
}

##END Farms###

# Combine sleptFarms, sleptForests
sleptForestsAwayM$Place <- rep("Forests",nrow(sleptForestsAwayM))
sleptFarmsAwayM$Place <- rep("Farms",nrow(sleptFarmsAwayM))
tmp4 <- rbind(sleptForestsAwayM[!duplicated(sleptForestsAwayM[c("fileID","ConsecutiveDaysAway")]),], sleptFarmsAwayM[!duplicated(sleptFarmsAwayM[c("fileID","ConsecutiveDaysAway")]),])

# Prepare manual jitter for Fig 5
tmp4$dup <- duplicated(tmp4$fileID)
tmp4[order(tmp4$fileID),]

forestsTmp4 <- tmp4[tmp4$Place=="Forests",]
farmsTmp4 <- tmp4[tmp4$Place=="Farms",]
adjVal <- 0.09 # manual jitter level

forestsTmp4$samePos <- duplicated(paste0(forestsTmp4$ConsecutiveDaysAway, forestsTmp4$Frequency)) #duplicated on ConsecutiveDaysAway and Frequency
forestsTmp4$duplicatedId <- duplicated(forestsTmp4$fileID)
forestsTmp4$xVal <- as.numeric(forestsTmp4$ConsecutiveDaysAway)

# Adjust point positions according to "adjVal" [forests]
for(i in unique(forestsTmp4$ConsecutiveDaysAway)){
  frequencyValues <- rep(0, 10)
  for(j in 1:nrow(forestsTmp4)){
    if(forestsTmp4$ConsecutiveDaysAway[j]==i && forestsTmp4$samePos[j]==TRUE){
      frequencyValues[forestsTmp4$Frequency[j]] <- frequencyValues[forestsTmp4$Frequency[j]]+1
      flrVal <- floor(frequencyValues[forestsTmp4$Frequency[j]]/2)
      if(frequencyValues[forestsTmp4$Frequency[j]] %% 2== 0){
        forestsTmp4$xVal[j] <- forestsTmp4$xVal[j] - ((frequencyValues[forestsTmp4$Frequency[j]]-flrVal) * adjVal)
      } else {
        forestsTmp4$xVal[j] <- forestsTmp4$xVal[j] + ((frequencyValues[forestsTmp4$Frequency[j]]-flrVal) * adjVal)
      }
    }
  }
}

farmsTmp4$samePos <- duplicated(paste0(farmsTmp4$ConsecutiveDaysAway, farmsTmp4$Frequency)) #duplicated on ConsecutiveDaysAway and Frequency
farmsTmp4$duplicatedId <- duplicated(farmsTmp4$fileID)
farmsTmp4$xVal <- as.numeric(farmsTmp4$ConsecutiveDaysAway)

# Adjust point positions according to "adjVal" [farms]
for(i in unique(farmsTmp4$ConsecutiveDaysAway)){
  frequencyValues <- rep(0, 10)
  for(j in 1:nrow(farmsTmp4)){
    if(farmsTmp4$ConsecutiveDaysAway[j]==i && farmsTmp4$samePos[j]==TRUE){
      frequencyValues[farmsTmp4$Frequency[j]] <- frequencyValues[farmsTmp4$Frequency[j]]+1
      flrVal <- floor(frequencyValues[farmsTmp4$Frequency[j]]/2)
      if(frequencyValues[farmsTmp4$Frequency[j]] %% 2== 0){
        farmsTmp4$xVal[j] <- farmsTmp4$xVal[j] - ((frequencyValues[farmsTmp4$Frequency[j]]-flrVal) * adjVal)
      } else {
        farmsTmp4$xVal[j] <- farmsTmp4$xVal[j] + ((frequencyValues[farmsTmp4$Frequency[j]]-flrVal) * adjVal)
      }
    }
  }
}

tmp5 <- rbind(forestsTmp4, farmsTmp4)
ConsXlab <- levels(tmp5$ConsecutiveDaysAway)

png(filename = "output/summarizeDemo/Fig5.png", width = 1800, height=1000, units="px")
gFig5 <- ggplot(tmp5, aes(x=xVal, y=Frequency))+
  geom_point(aes(shape=factor(Sex, levels=c("M","F")), col=factor(ageGp,levels=c("<20","20-40",">=40"))), size=15)+
  geom_path(aes(group=fileID), alpha=0.7, linetype=2)+
  facet_grid(.~Place)+
  scale_shape_manual(name="Gender", values=sexColVal)+scale_color_manual(name="Age group", values=ageShapeVal)+ #c(15, 1, 2))+
  xlab("No. of consecutive nights at the farms and the forests")+
  scale_x_continuous(labels = ConsXlab)+
  scale_y_continuous(name="Count", breaks=seq(0,10,2))+
  theme_bw(base_size = 35)
gFig5
dev.off()


#---------------------------------------------------------------------------------------------------

### - Mixed-effects model (Table 2) ###

# Negative-binomial generalized linear mixed-effects model was used to investigate potential 
# associations between the total number of nights spent in the farms or forests.

# Extract nights slept in different places for Dry and Rainy seasons
resultsDry <- data.frame(matrix(NA, nrow=length(fileIDindex), ncol=5))
resultsRainy <- data.frame(matrix(NA, nrow=length(fileIDindex), ncol=5))

for(i in 1:length(fileIDindex)){
  sleptPlace <- slept[slept$fileID==fileIDindex[i],]
  homePlace <- housesBuffer[housesBuffer$fileID==fileIDindex[i],]
  
  #Dry
  daysSleptHomeDry <- (sleptPlace[homePlace,]$Date <= "2017/05/16" | sleptPlace[homePlace,]$Date >="2017/10/16") %>% sum
  daysSleptForestDry <- (sleptPlace[forests,]$Date <= "2017/05/16" | sleptPlace[forests,]$Date >="2017/10/16") %>% sum
  daysSleptFarmDry <- (sleptPlace[farms,]$Date <= "2017/05/16" | sleptPlace[farms,]$Date >="2017/10/16") %>% sum
  daysParticipatedDry <- (sleptPlace$Date <= "2017/05/16" | sleptPlace$Date >="2017/10/16") %>% sum
  
  #Rainy
  daysSleptHomeRainy <- (sleptPlace[homePlace,]$Date > "2017/05/16" & sleptPlace[homePlace,]$Date <"2017/10/16") %>% sum
  daysSleptForestRainy <- (sleptPlace[forests,]$Date > "2017/05/16" & sleptPlace[forests,]$Date <"2017/10/16") %>% sum
  daysSleptFarmRainy <- (sleptPlace[farms,]$Date > "2017/05/16" & sleptPlace[farms,]$Date <"2017/10/16") %>% sum
  daysParticipatedRainy <- (sleptPlace$Date > "2017/05/16" & sleptPlace$Date <"2017/10/16") %>% sum
  
  resultsDry[i,] <- cbind(fileIDindex[i], daysParticipatedDry, daysSleptHomeDry, daysSleptFarmDry, daysSleptForestDry)
  resultsRainy[i,] <- cbind(fileIDindex[i], daysParticipatedRainy, daysSleptHomeRainy, daysSleptFarmRainy, daysSleptForestRainy)
}

names(resultsRainy) <- names(resultsDry) <- c("fileID", "daysParticipated","daysSleptHome", "daysSleptFarm", "daysSleptForest")

#include only those particiapted over 30 days in a season 
resultsDry <- resultsDry[resultsDry$daysParticipated>30,]
resultsRainy <- resultsRainy[resultsRainy$daysParticipated>30,]

#create percentages
resultsDry$Home <- resultsDry$daysSleptHome/resultsDry$daysParticipated
resultsDry$Farms <- resultsDry$daysSleptFarm/resultsDry$daysParticipated
resultsDry$Forests <- resultsDry$daysSleptForest/resultsDry$daysParticipated

resultsRainy$Home <- resultsRainy$daysSleptHome/resultsRainy$daysParticipated
resultsRainy$Farms <- resultsRainy$daysSleptFarm/resultsRainy$daysParticipated
resultsRainy$Forests <- resultsRainy$daysSleptForest/resultsRainy$daysParticipated

# Construct data frame for the linear model
demoDataSleptDry <- merge(demoData, resultsDry, by.y="fileID", by.x="pid")
demoDataSleptDry$season <- rep("Dry", nrow(demoDataSleptDry))
demoDataSleptRainy <- merge(demoData, resultsRainy, by.y="fileID", by.x="pid")
demoDataSleptRainy$season <- rep("Rainy", nrow(demoDataSleptRainy))
demoDataSleptBySeason <- rbind(demoDataSleptDry, demoDataSleptRainy)

# Create model
modelForest <- glmer.nb(daysSleptForest ~ ageGp + Sex + (1|pid) + season, data=demoDataSleptBySeason)
modelFarm <- glmer.nb(daysSleptFarm ~ ageGp + Sex + (1|pid) + season, data=demoDataSleptBySeason)
#summary(modelForest)
#exp(confint(modelForest, method="Wald"))

# Generate Table 2
tab_model(modelFarm, modelForest)


#---------------------------------------------------------------------------------------------------