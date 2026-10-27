module

public import Certificates.Data.Kernel.Cert690.Base
public import Certificates.Kernel.Cert690.GrpPData

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelC690.GrpP

open CFSG.KC.C690

set_option maxHeartbeats 0 in
theorem bfsNegEntry : bfsOK (fun y => (idxT S).find y O.length)
    [34647329153, 35704297409, 34630292097, 34630549889, 17717821506] (O.set 7 (O[8]!)) par =
    false := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem bfsNegPar : bfsOK (fun y => (idxT S).find y O.length)
    [34647329153, 35704297409, 34630292097, 34630549889, 17717821506] O (par.set 7 (0, 4)) =
    false := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem bfsNegGen : bfsOK (fun y => (idxT S).find y O.length)
    [34647329153, 35704297409, 34630292097, 34630549889] O par = false := by
  decide +kernel

end CertificateChecks.KernelC690.GrpP

end
