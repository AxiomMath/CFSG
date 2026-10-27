module

public import Certificates.Data.Kernel.Cert690.CBase
public import Certificates.Data.Smith1979W3.CensusData
public import Certificates.Kernel.Cert690.GrpMData

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelC690.GrpM

open CFSG.KC.C690 CFSG.GF2Type.Smith1979W3.Cert690

set_option maxHeartbeats 0 in
theorem transM : transK (gkOf O S inv 51840) (singL true) (b0Of true)
    (transWitK (gkOf O S inv 51840) (singL true) (b0Of true)) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem lsM : censusLsK (gkOf O S inv 51840) true (ldata true ()) = true := by decide +kernel

end CertificateChecks.KernelC690.GrpM

end
