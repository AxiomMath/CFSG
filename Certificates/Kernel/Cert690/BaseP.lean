module

public import Certificates.Data.Kernel.Cert690.CBase
public import Certificates.Data.Smith1979W3.CensusData
public import Certificates.Kernel.Cert690.GrpPData

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelC690.GrpP

open CFSG.KC.C690 CFSG.GF2Type.Smith1979W3.Cert690

set_option maxHeartbeats 0 in
theorem transP : transK (gkOf O S inv 40320) (singL false) (b0Of false)
    (transWitK (gkOf O S inv 40320) (singL false) (b0Of false)) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem lsP : censusLsK (gkOf O S inv 40320) false (ldata false ()) = true := by decide +kernel

end CertificateChecks.KernelC690.GrpP

end
