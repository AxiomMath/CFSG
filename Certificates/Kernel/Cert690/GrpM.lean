module

public import Certificates.Data.Kernel.Cert690.Base
public import Certificates.Kernel.Cert690.GrpMData

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelC690.GrpM

open CFSG.KC.C690

theorem lenO : O.length = 51840 := by decide +kernel

theorem lenOm : Om.length = 25920 := by decide +kernel

set_option maxHeartbeats 0 in
theorem ixO : ixOK S O = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ixOm : ixOK Sm Om = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem bfsO : bfsOK (fun y => (idxT S).find y O.length)
    [35721076609, 35720809665, 35704292801, 35704030401, 17717821506] O par = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem bfsOm : bfsOK (fun y => (idxT Sm).find y Om.length)
    [35721076609, 35720809665, 35704292801, 35704030401, 17718853698] Om omPar = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem invO : invK (idxT S) O.length O inv = true := by decide +kernel

end CertificateChecks.KernelC690.GrpM

end
