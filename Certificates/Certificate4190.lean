
module

public import Certificates.Certificate4190Base

public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsGeoDAct
public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsGeoPtLoc
public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsGeoLnLoc
import Certificates.Kernel.TitsD.Glue

public section

public section

namespace Certificates

open CertificateChecks

open CFSG.Quasithin CFSG.Sporadic.Schreier.Tits CFSG.Quasithin.H13.F45Ru CFSG.Quasithin.TitsGeo in
theorem certificate4190 : titsGeoFacts :=
  KernelTitsD.facts4190

end Certificates
