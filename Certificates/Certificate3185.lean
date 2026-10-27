module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylBridgeData
import Certificates.Kernel.LocalComp.Weyl3185

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.OmegaEight.Weyl in
theorem certificate3185 : (pairCheck = true)
    ∧ (zWordCheck = true)
    ∧ (omCheck = true)
    ∧ (sZeroCheck = true)
    ∧ (trialityCheck = true) := KernelLC.W3185.cert3185

end Certificates
