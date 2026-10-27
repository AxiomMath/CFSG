module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylUData
import Certificates.Kernel.LocalComp.Weyl3222

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.OmegaEight.Weyl in
theorem certificate3222 : (uniqueCheck = true)
    ∧ (centerCCheck = true)
    ∧ (centerModCheck = true)
    ∧ (commSetCheck = true) := KernelLC.W3186.cert3222

end Certificates
