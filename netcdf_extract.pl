#!/usr/bin/perl

use strict;
use DBI;
use Getopt::Long;
use Date::Manip;
use PDL;
use PDL::NetCDF;
use List::Util;

require "ora.pl";

  &Usage if $#ARGV < 0;

  our ($dbh, $sth, $sql, %row);
  our ($basedir, $user, $getvars, 
    $fromdate, $todate, $sitelist, $force, $check, $verbose);

  my $debug;

  &GetOptions('help|?'=>\&Usage,
              'dir=s'=>\$basedir,
              'variables=s'=>\$getvars,
              'check'=>\$check,
              'fromdate=s'=>\$fromdate,
              'todate=s'=>\$todate,
              'sitelist=s'=>\$sitelist,
              'xforce'=>\$force,
              'debug'=>\$debug,
                );

  sub Usage {
    print "\nUsage: $0 [options] <day|month|year> <week|hour> <variable> [variable...]
      -from = beginning date to extract (default beginning of model year)
      -to = beginning date to extract [end of model year)
      -d = directory [current directory]
      -v = get variables from CMAQ_VARIABLES
      -s = siteid1,siteid2,...
      -x = overwrite csv file
      -c = check to see if variables are complete
    ";
    
    exit 0;
  }
  
########################################################
### Connect to Oracle
  $user = 'CMAQ' if not $user;  
  &Connect($user);
  my $passwd= &Passwd($user);

###########################################################

########################################################
###  define variables
  my $oraVariables="CMAQ.CMAQ_VARIABLES";
  my $newtz='EST';
  my $filetz='GMT';
  my $extdir = '/data/cmaq/external_tables';
  my $ncperiod = lc shift @ARGV;
  my $agglevel = lc shift @ARGV;
  
  &Usage unless $agglevel =~ /hour|week/;

  $basedir = $ENV{PWD} unless $basedir;
  $basedir .= '/' unless $basedir =~/\/$/;
  
  our ($year,$domain)=&RunVariables($basedir);

   # Get the variables
  my @variables;

  if ($getvars) {
    (@variables) = &VariableList($basedir,$getvars);
  }
  else {
    @variables = map uc, @ARGV;
  }
  
  my ($stat, $filebase) = &VarAttributes($basedir,$ncperiod,@variables);

  &Usage unless @variables;

  $agglevel=~ tr/A-Z/a-z/;
  
  $fromdate = ParseDate("$fromdate") or 
    $fromdate = ParseDate("01/01/$year");
  $todate = ParseDate("$todate") or 
    $todate = ParseDate("12/31/$year 23:00");
  
  print "Aggregating $agglevel from '$basedir'\n";
  print "Date Range: $fromdate to $todate\n";
  print "Variables: @variables\n";
  

########################################################

  #number of hours in each interval
  my %hours = (
    day	=> 24,
    week	=> 168,
  );
  
  #the first hour in the day for each interval
  my %firstHour = (
    day	=> 0,
    week	=> 9,
  );
  
########################################################
### Main dependent variables

  my (
     %csvfile,		# variable CSV file 
     %fh, 		# variable filehandles
     %error,		# errors in execution by variable
     @coord,		# coln,rown of site coordinates
     $rows,		# number of rows in file
     $pdlIndex, 	# PDL of index coordinates for sites
  );

### Main

  
  &CheckFiles if $check;
  
  foreach my $var (@variables) {
    $csvfile{$var} = lc "$var.$agglevel.csv";
    &ManageCSV($csvfile{$var});
    &OpenCSV($var,$csvfile{$var});
  }
  
  ($pdlIndex,@coord) = &PdlIndex(split ',',uc $sitelist) if $sitelist;
  
  if ($agglevel eq 'hour') {
    &ExtractHours ;
  }
  else {
    &ExtractAggregate;
  }

  foreach my $var (@variables) {
      &PrintSQL($agglevel,$basedir,$var);
      close $fh{$var};
      &OraUpdate($basedir,$var) if ($getvars) ;
  }
  
  print "\n";
  

#####################################################
### End Main
#####################################################

#####################################################
### Main Extraction subroutines
#####################################################

sub ExtractAggregate {

  ### Calculate averages and sums for an aggregate period

  my (
     $dateon,		# datetime period begins
     $dateoff,		# datetime period ends
     $sdate,		# file start date
     $nextdate,	# date for next file
     $ncFilename,	# NetCDF filename
     $ncLastDate,   # Last date in NetCDF file
     $lastFilename, # Name of last NC file opened
     $firstTue, 	# first Tuesday of year
     $hourOn,		# hours of year period begins
     $hourOff,		# hours of year period ends
     $hoursInFile,	# Hours in ncfile
     $hoursInDay,   # hours in day
     $hoursInMonth, # hours in month
     $hoursInLast,	# hours in previous incomplete period
     $hoursInYear,	# hours in the model run year
     $month,		# numerical month of year
     $cols, $rows, $layers, 		# dimmensions of pdl
     $dateBegin,	# date series begins in localtime
     %pdl,		# pdl containing variable matrix
     %pdlAvg,		# pdl containing average for period
     %pdlSum,		# pdl containing sum for period
     %pdlPeriod,	# pdl containing all hours in period for variable
  );
  
  ### find the start and end times for all periods in CMAQ time
  my (@dateon_list, @dateons, %dateoffs);
  $firstTue = Date_GetNext($fromdate,'Tuesday',2,$firstHour{$agglevel});
  $firstTue = Date_ConvTZ($firstTue,"$newtz","$filetz");

# A cluge to get around missing file for 1/3/2006 for first week of year
#    $firstTue =DateCalc($firstTue,"+24 hour");

  for (my $day=$firstTue; Date_Cmp($day,$todate)<0; $day=DateCalc($day,"+1 week")) {
    push @dateon_list,$day;
    $dateoffs{$day}=DateCalc($day,"+167 hour");
    # Don't go beyond last day of period even if partial
    $dateoffs{$day}=$todate if Date_Cmp(DateCalc($day,"+167 hour"),$todate)>=0;
    print "DAY=$day: $dateoffs{$day}\n" if $debug;
  }

  # We reuse the dateon_list for each variable
  @dateons=@dateon_list;

  # Extract data for each period starting with the dateon
  while (my $dateon = shift @dateons) {

    my ( $hoursCumm,  # cummulative total of hours in period
        %pdlCumm,     # cummulative sum 
        );

    my $dateoff = $dateoffs{$dateon};
    print "$dateon to $dateoff:\n";
    $nextdate=$dateon;

    ### Extract each of the variables from the ncfile
    # Figure out the name of the IOAPI file for each period
    $ncFilename = &FileName($dateon);

    ($sdate,%pdl)=&PdlVar($ncFilename,@variables)
          if $lastFilename ne $ncFilename;
    $lastFilename = $ncFilename;
         
    # Get the dimensions of the the first variable PDL 
    ($cols,$rows,$layers,$hoursInFile) = dims $pdl{$variables[0]};

    $ncLastDate = DateCalc($sdate,"+$hoursInFile hour");

    # while last date in file is less than dateoff 
    # i.e., the period extends beyond the file hours
    while (Date_Cmp($ncLastDate,$dateoff) <0 ) {
      # number of hours from beginning of file to dateon
      $hourOn = Delta_Format( DateCalc($sdate,$nextdate),2,"%hh");
      $hourOff = $hoursInFile - 1;
      $hoursCumm = 1+ $hoursCumm + $hourOff - $hourOn;

      print "\t$sdate,$hoursInFile,$ncLastDate,$nextdate\n" if $debug;
      print "\t$hourOn-$hourOff => $hoursCumm ";
 
      foreach my $var (@variables) {
        # Create the PDL for the time period and add it to the running total
        print "$var " if $debug;
        $pdlPeriod{$var} = slice $pdl{$var},":,:,:,$hourOn:$hourOff";
        $pdlSum{$var} = sumover(mv($pdlPeriod{$var},3,0)) + $pdlCumm{$var};
        $pdlCumm{$var} = $pdlSum{$var};
      }
      print "\n";
      
      # Figure out what the next file is
      $nextdate = &CheckLeapDay($ncLastDate);
      $ncFilename = &FileName($nextdate);

      ($sdate,%pdl)=&PdlVar($ncFilename,@variables)
          if $lastFilename ne $ncFilename;
      $lastFilename = $ncFilename;
          
      ($cols,$rows,$layers,$hoursInFile) = dims $pdl{$variables[0]};
      $ncLastDate = DateCalc($sdate,"+$hoursInFile hour");
    }

    # use same pdl while ncDateoff >= dateoff
    $hourOn = Delta_Format( DateCalc($sdate,$nextdate),2,"%hh");
    $hourOff= &HourOff($sdate,$hoursInFile,$dateoff);
    $hoursCumm = 1 + $hoursCumm + $hourOff - $hourOn;

    print "\t$hourOn-$hourOff => $hoursCumm ";

    foreach my $var (@variables) {
      # Create the PDL for the time period and add it to the running total
      print "$var " if $debug;
      $pdlPeriod{$var} = slice $pdl{$var},":,:,:,$hourOn:$hourOff";
      $pdlSum{$var} = sumover(mv($pdlPeriod{$var},3,0)) 
          * $hours{$agglevel}/$hoursCumm  
          + $pdlCumm{$var};
      $pdlAvg{$var} = $pdlSum{$var}/($hoursCumm);

      my %pdlOut = (
        'sum' => $pdlSum{$var},
        'avg' => $pdlAvg{$var},
        'debug' => $pdlPeriod{$var},
        );
      my $pdl = $pdlOut{$stat};

      &Export_Data(
          $var, 
          $pdl,
          Date_ConvTZ($dateon,$filetz,$newtz),
          Date_ConvTZ($dateoff,$filetz,$newtz),
          $rows,
          $cols) ;

    }  # foreach var
    print "\n";
    warn "\tWARNING: hoursInPeriod='$hoursCumm'\n" if $hoursCumm ne $hours{$agglevel};

  } # foreach dateon

  sub Export_Data {
     # Exports data from a PDL to CSV file
      my ($var,$pdl,$dateon,$dateoff,$rows,$cols) = @_;

      my ($pdlSlice, @values);

      my @col_list=(0..$cols-1);
      my @row_list=(0..$rows-1);

      foreach my $col (@col_list) {
        $pdlSlice = slice($pdl, "$col");
        @values = list $pdlSlice;
        foreach my $row (@row_list) {
          print {$fh{$var}} "$var,$dateon,$dateoff,$col,$row,$values[$row]\n";
        }
      }
  }
  
  sub HourOff {
    # Returns the houroff for the slice
    my ($startdate, $hoursinfile, $dateoff) = @_;
    my $datetest = Date_Cmp( DateCalc($startdate,"+$hoursinfile hour"),$dateoff);

    if ($datetest<0) {
      # The period extends beyond the file hours
      return $hoursinfile-1;
    }
    elsif ($datetest eq 0) {
      # the hour matching the dateoff
      return Delta_Format( DateCalc($startdate,$dateoff),2,"%hh") - 1;
    }
    else {
      # the hour matching the dateoff
      return Delta_Format( DateCalc($startdate,$dateoff),2,"%hh");
    }
  }

}

sub ExtractHours {

### Extracts hourly values for the variable list
  
  my (
     $dateoff,		# datetime period begins and ends
     $hourOff,		# hour offset in file
     $sdate,		# file start date
     $ncFilename,		# NetCDF filename
     $lastFilename,  # the last NetCDF file opened
     $hoursInFile,	# Hours in ncfile
     $hoursInDay,   # hours in day
     $hoursInMonth, # hours in month
     $cols, $rows, $layers, 		# dimmensions of pdl
     $dateBegin,	# date series begins in localtime
     $pdlPeriod,	# pdl for the hour
     %pdl,		# pdl containing variable matrix
     $ncPeriod,	# time period of nc file (month, day or year)
  );
  
  # Step $filetime through each hour from $fromdate to $todate
    for (my $filetime=$fromdate; 
          Date_Cmp($filetime,$todate)<=0; 
          $filetime=DateCalc($filetime,"+1 hour")) {

      # Convert filetime from UTC to localtime
      $dateoff=Date_ConvTZ( $filetime,$filetz,$newtz);

      $ncFilename = &FileName($filetime);

      ($sdate,%pdl)=&PdlVar($ncFilename,@variables)
          if $lastFilename ne $ncFilename;
      $lastFilename = $ncFilename;

      $hourOff = Delta_Format( DateCalc($sdate,$filetime),2,"%hh");

      print "\t$ncFilename\t$dateoff (+$hourOff) ";

      next if Date_Cmp($filetime,$sdate)<0;
      # Skip leap day
      next if UnixDate($filetime,"%m%d") eq "0229";

      ($cols,$rows,$layers,$hoursInFile) = dims $pdl{$variables[0]};

      foreach my $var (@variables) {
        print "$var " if $debug;

        $pdlPeriod = slice $pdl{$var},":,:,:,$hourOff:$hourOff";

        if ($sitelist) {
          my @values = list $pdlPeriod->range($pdlIndex);
          foreach my $n (0..$#coord) {
            my ($col,$row) = @{$coord[$n]};
            print {$fh{$var}} "$var,$dateoff,$col,$row,$values[$n],$hourOff\n";
          }

        }
        else {
          my @col_list=(0..$cols-1);
          my @row_list=(0..$rows-1);

          foreach my $col (@col_list) { 
             my $pdlSlice = slice($pdlPeriod, "$col");
             my @values = list $pdlSlice;
             foreach my $row (@row_list ) { 
                print {$fh{$var}} "$var,$dateoff,$col,$row,$values[$row],$hourOff\n";
             }
          }
        }

      }  # end variables

      print "\n";
  } # end filetime

}  # End 

#####################################################
### Utility subroutines
#####################################################

sub CheckFiles {
### Checks NetCDF files for variables

  my $errfile=lc "missing_files.txt";

  print "Checking files:\n";

  my  $firstTue = Date_GetNext($fromdate,'Tuesday',2,$firstHour{$agglevel});
  my  $firstTue = Date_ConvTZ($firstTue,"$newtz","$filetz");

  my %unique;
  for (my $day=$firstTue; 
    Date_Cmp($day,$todate)<0; 
    $day=DateCalc($day,"+1 day")) 
  {
    foreach my $var (@variables) {
      my $filename = &FileName($day);
      $unique{$filename}=1;
      # print "$var,$day,$filename\n";
    }
  }
  
  my $nc;
  my $message;

  foreach my $ncfile (sort keys %unique) {

     print "$ncfile\n";
     if (-e $ncfile) {
       $nc = PDL::NetCDF->new(
           $ncfile,
           {MODE=>"O_RDONLY"}
       )
     }
     else {
        $message .= "$ncfile missing\n";
     }

     my @varlist = @{$nc->getvariablenames()};
     foreach my $var (@variables) {
       if (! grep (/$var/,@varlist)) {
         $message .= "$ncfile:$var missing\n";
       }
     }
  }

  if ($message) {
    open ERRFILE, ">$errfile" or die "Couldn't open $errfile\n";
    print ERRFILE $message;
    close ERRFILE;
  }
  else {
    print "Variables are complete\n"
  }

  exit 0;
}

sub FileName {
  # Find the right NetCDF filename for the variable and date
  my ($date) = @_;
  my %ending = (
    day => '%Y%m%d',
    month => '%m',
    year => '%Y',
  );

  my $suffix = UnixDate($date,"$ending{$ncperiod}");
  return "$filebase.$suffix";
}

sub CheckLeapDay {
  # Returns the next day if day is a leap day 
  # otherwise returns the same day
  my ($date) = @_;

  if (UnixDate($date,"%m%d") eq "0229") {
    print "\tWARNING: Skipping leap day $date\n";
    return DateCalc($date,"+1 day");
  }
  else {
    return $date
  }

}

sub ManageCSV {
  ## Names and opens the CSV output file
  my ($filename)=@_;

  if (-e $filename and $force) {
      system "rm $filename" ;
  }
  elsif (-e $filename) {
    print "Delete existing $filename ? ";
    if (<STDIN>=~/^y/i) {
      system "rm $filename" ;
    }
    else {warn "Appending data to $filename\n";}
  }
}

sub OpenCSV {
  ## Names and opens the CSV output file
  my ($var,$filename)=@_;

  print "Opening $filename\n" if $debug;
  open $fh{$var}, ">>$filename" or die "Couldn't open $filename\n";
  return($filename);
}

sub OraUpdate {
  # Updates the list of variables in oracle table
    my ($dir,$var) = @_;

   print "Updating $var in $oraVariables\n";
   $sql = "UPDATE $oraVariables
   SET status=status+1 
   WHERE variable='$var'
     AND dir='$dir'";

   # print "$sql\n";
   $sth = $dbh->prepare($sql);
   $sth->execute or die "$sth->errstr\n";
    
}

sub PdlIndex {
# Creates an index PDL for sites in the site list 
  my (@list) = @_;
  
  map {s/(.+)/\'$1\'/} @list;
  my $sitelist = join ',',@list;
  my $oraCoordinates = "CMAQ.COORD_$domain\_NETWORKS_MV";
  my (@sites,@colrow);

   $sql = "SELECT site_id, coln, rown
   FROM $oraCoordinates
   WHERE site_id IN ($sitelist)";

   # print "$sql\n";
   $sth = $dbh->prepare($sql);
   $sth->execute or die "$sth->errstr\n";

   my %row;
   $sth->bind_columns(\( @row{ @{$sth->{NAME_lc} } } ));

   print "Extracting locations for:\n";
   while ($sth->fetch) {
       print "\t$row{site_id}= $row{coln},$row{rown}\n";
       push @sites,$row{site_id};
       push @colrow,[$row{coln},$row{rown}];
   }

  return pdl(@colrow), @colrow;
}  # End 

sub PdlVar {
  # Gets the variable PDLs from the NetCDF file
  my ($ncfile,@variables)=@_;
  my %pdl;
  
  die "ERROR: Can't find $ncfile\n" unless -f $ncfile;
  
  my $nc = PDL::NetCDF->new(
      $ncfile,
      {MODE=>"O_RDONLY"},
  ) or warn "*** ERROR: Couldn't open $ncfile \n" ;

  my @varlist = @{$nc->getvariablenames()};
  my $sdate = ParseDate(list $nc->getatt('SDATE'));

  print "\tGetting PDLs from $ncfile for ";
  foreach my $var (@variables) {
    print "$var ";
    if (grep (/$var/,@varlist)) {
      $pdl{$var} = $nc->get($var);
    }
    else {
      warn "ERROR: $var missing from $ncfile\n";
    }
  }
  print "\n";
  return ($sdate,%pdl);
}

sub PrintSQL {
  #Prints the SQL needed to load the extracted data
  my ($agglevel,$dir,$var)=@_;
  my $sqlfile = lc "$var.$agglevel.sql";
  my $extdir = "/data/cmaq/external_tables";
  
   $sql = "SELECT table_name
     FROM  CMAQ.CMAQ_PARENT_TABLES
     WHERE dir='$dir' AND agg_period='$agglevel'";

   # print "$sql\n";
   $sth = $dbh->prepare($sql);
   $sth->execute or die "$sth->errstr\n";

   my %row;
   $sth->bind_columns(\( @row{ @{$sth->{NAME_lc} } } ));

   $sth->fetch;
   
   warn "WARNING: Parent table not found for '$dir/$agglevel'\n" if $sth->rows eq 0;

  # External tables to load from
  my %extTables=(
    week=>'LOAD_EXTERNAL',
    hour=>'LOAD_HOURLY_EXTERNAL',
    day=>'LOAD_EXTERNAL',
    );

  my $extfile=lc "$extdir/$extTables{$agglevel}.csv"  ;
  my $exttable = $extTables{$agglevel};

  my $cmd = "
/*** $var ***/

ALTER TABLE CMAQ.$exttable
LOCATION (CMAQ:'$csvfile{$var}')
;

INSERT INTO $row{table_name}
SELECT * FROM $extTables{$agglevel}
;

COMMIT;
";

  open SQL, ">$sqlfile";
  print SQL "$cmd\n";
  close SQL;

}

sub RunVariables {
   ## Gets the variable attributes from Oracle tables
   my ($dir) =@_;

   $sql = "SELECT model_year, domain
     FROM  CMAQ.CMAQ_RUNS
     WHERE dir='$dir'";

   # print "$sql\n";
   $sth = $dbh->prepare($sql);
   $sth->execute or die "$sth->errstr\n";

   my %row;
   $sth->bind_columns(\( @row{ @{$sth->{NAME_lc} } } ));

   $sth->fetch;
   
   die "ERROR: Run variables not found for '$dir'\n" if $sth->rows eq 0;
   print "Run variables: year=$row{model_year} domain=$row{domain}\n";
   return($row{model_year}, $row{domain});

}

sub VarAttributes {
  # Gets the list of variables attributes from oracle table
    my ($dir,$fileperiod,@varlist) = @_;
    my (%stats,%filebases);
    
    map {s/(.+)/\'$1\'/} @varlist;
    my $varlist = join ',',@varlist;

    print "Getting attributes from $oraVariables\n";
    
   $sql = "SELECT variable
   , media
   , DECODE(media,'dep','sum','avg') stat
   , filebase 
   FROM $oraVariables
   WHERE dir='$dir' 
   AND period='$fileperiod'
   AND variable in ($varlist)";

   $sth = $dbh->prepare($sql);
   $sth->execute or die "$sth->errstr\n";

   my %row;
   $sth->bind_columns(\( @row{ @{$sth->{NAME_lc} } } ));

   # Check that variables are of the same type
   while ($sth->fetch) {
       $stats{$row{stat}}=1;
       $filebases{$row{filebase}}=1;
       print "\t$row{variable},$row{stat},$row{filebase}\n";
   }

   die "ERROR: Found attributes for ",$sth->rows," variables, expecting ",$#varlist + 1," from:
        $sql\n" if $sth->rows ne $#varlist + 1;
    
  my @attributes = (keys %stats, keys %filebases);

  die "ERROR: Variable attributes must be consistent\n" 
    unless $#attributes eq 1;
  return @attributes;
  
}

sub VariableList {
  # Gets the list of variables from oracle table
    my ($dir,$status) = @_;
    my @variables;
    print "Getting variables from $oraVariables\n";
   $sql = "SELECT variable FROM $oraVariables
   WHERE status=$status 
   AND dir='$dir'";

   # print "$sql\n";
   $sth = $dbh->prepare($sql);
   $sth->execute or die "$sth->errstr\n";

   my %row;
   $sth->bind_columns(\( @row{ @{$sth->{NAME_lc} } } ));

   while ($sth->fetch) {
       push @variables,$row{variable};
   }
   return @variables;
    
}



