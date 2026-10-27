module

public import Certificates.Data.Kernel.Cert690.Enum
public import Certificates.Kernel.Cert690.GrpMData

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelC690.GrpM

open CFSG.KC.C690

set_option maxHeartbeats 0 in
theorem parO : enumParK (fun i => (posT O).find i 0)
    [35721076609, 35720809665, 35704292801, 35704030401, 17717821506] O par 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem clO : enumClK (fun y => (idxT S).find y O.length) O.length
    [35721076609, 35720809665, 35704292801, 35704030401, 17717821506] O = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem invGO : enumInvK [35721076609, 35720809665, 35704292801, 35704030401, 17717821506] O =
    true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem parOm : enumParK (fun i => (posT Om).find i 0)
    [35721076609, 35720809665, 35704292801, 35704030401, 17718853698] Om omPar 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem clOm : enumClK (fun y => (idxT Sm).find y Om.length) Om.length
    [35721076609, 35720809665, 35704292801, 35704030401, 17718853698] Om = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem invGOm : enumInvK [35721076609, 35720809665, 35704292801, 35704030401, 17718853698] Om =
    true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem invMul : invMulK (fun i => (posT O).find i 0) 51840 O inv = true := by decide +kernel

end CertificateChecks.KernelC690.GrpM

end
