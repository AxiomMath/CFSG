module

public import Certificates.Data.Kernel.Cert690.Base
public import Certificates.Kernel.Cert690.GrpPData

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelC690.GrpP

open CFSG.KC.C690

theorem lenO : O.length = 40320 := by decide +kernel

theorem lenOm : Om.length = 20160 := by decide +kernel

set_option maxHeartbeats 0 in
theorem ixO : ixOK S O = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ixOm : ixOK Sm Om = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem bfsO : bfsOK (fun y => (idxT S).find y O.length)
    [34647329153, 35704297409, 34630292097, 34630549889, 17717821506] O par = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem bfsOm : bfsOK (fun y => (idxT Sm).find y Om.length)
    [34647329153, 35704297409, 34630292097, 34630549889, 34629255234] Om omPar = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem invO : invK (idxT S) O.length O inv = true := by decide +kernel

end CertificateChecks.KernelC690.GrpP

end
