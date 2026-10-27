module

public import CFSG.Sporadic.HNSchreier.Schreier
public import CFSG.LocalAnalysis.ComponentClassification.SporadicSchreierDispatch
public import Certificates.Certificate2096
public import Certificates.Certificate2097
public import Certificates.Certificate2098
public import Certificates.Certificate2099
public import Certificates.Certificate2100
public import Certificates.Certificate2102
public import Certificates.Certificate2103
public import Certificates.Certificate2104
public import Certificates.Certificate2107
public import Certificates.Certificate2108
public import Certificates.Certificate2109
public import Certificates.Certificate16041
public import CFSG.Sporadic.M23.M23Group

public section

namespace CFSG.Sporadic.HNSchreier

open CFSG.ComponentClassification.SporadicSchreierDispatch

theorem sporadicSchreierCase_HN :
    SporadicSchreierCase .HN :=
  sporadicSchreierCase_of_outer AT_HN_Schreier

end CFSG.Sporadic.HNSchreier
