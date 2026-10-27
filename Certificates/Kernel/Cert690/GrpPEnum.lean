module

public import Certificates.Data.Kernel.Cert690.Enum
public import Certificates.Kernel.Cert690.GrpPData

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelC690.GrpP

open CFSG.KC.C690

set_option maxHeartbeats 0 in
theorem parO : enumParK (fun i => (posT O).find i 0)
    [34647329153, 35704297409, 34630292097, 34630549889, 17717821506] O par 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem clO : enumClK (fun y => (idxT S).find y O.length) O.length
    [34647329153, 35704297409, 34630292097, 34630549889, 17717821506] O = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem invGO : enumInvK [34647329153, 35704297409, 34630292097, 34630549889, 17717821506] O =
    true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem parOm : enumParK (fun i => (posT Om).find i 0)
    [34647329153, 35704297409, 34630292097, 34630549889, 34629255234] Om omPar 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem clOm : enumClK (fun y => (idxT Sm).find y Om.length) Om.length
    [34647329153, 35704297409, 34630292097, 34630549889, 34629255234] Om = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem invGOm : enumInvK [34647329153, 35704297409, 34630292097, 34630549889, 34629255234] Om =
    true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem invMul : invMulK (fun i => (posT O).find i 0) 40320 O inv = true := by decide +kernel

end CertificateChecks.KernelC690.GrpP

end
