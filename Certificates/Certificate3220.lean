module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylCentData
import Certificates.Kernel.LocalComp.Weyl3220

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.OmegaEight.Weyl in
theorem certificate3220 : (dFixCheck = true)
    ∧ (sOrbitCheck = true)
    ∧ (frameReflCheck = true)
    ∧ (wt2FixCheck = true)
    ∧ (tripleCheck = true)
    ∧ (pairCheck2 = true) := KernelLC.W3220.cert3220

end Certificates
