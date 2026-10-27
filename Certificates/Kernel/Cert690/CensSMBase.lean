module

public import Certificates.Data.Kernel.Cert690.CensusSBase
public import Certificates.Data.Smith1979W3.CensusData
public import Certificates.Kernel.Cert690.GrpMData
public import Certificates.Kernel.Cert690.CensSMB

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelC690.CensSM

open CFSG.KC.C690 CFSG.KC.C690S CFSG.GF2Type.Smith1979W3.Cert690

set_option maxHeartbeats 0 in
theorem baseOK : baseS (gkOf GrpM.O GrpM.S GrpM.inv 51840) (ldata true ()).Llist cands base =
    true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem candsEq : (candidatesOf true (ldata true ()).Llist).toList = cands := by decide +kernel

theorem singEq : singL true = sing := by decide +kernel

theorem bEq : b0Of true = b := by decide +kernel

end CertificateChecks.KernelC690.CensSM

end
