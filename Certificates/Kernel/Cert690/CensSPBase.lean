module

public import Certificates.Data.Kernel.Cert690.CensusSBase
public import Certificates.Data.Smith1979W3.CensusData
public import Certificates.Kernel.Cert690.GrpPData
public import Certificates.Kernel.Cert690.CensSPB

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelC690.CensSP

open CFSG.KC.C690 CFSG.KC.C690S CFSG.GF2Type.Smith1979W3.Cert690

set_option maxHeartbeats 0 in
theorem baseOK : baseS (gkOf GrpP.O GrpP.S GrpP.inv 40320) (ldata false ()).Llist cands base =
    true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem candsEq : (candidatesOf false (ldata false ()).Llist).toList = cands := by decide +kernel

theorem singEq : singL false = sing := by decide +kernel

theorem bEq : b0Of false = b := by decide +kernel

end CertificateChecks.KernelC690.CensSP

end
