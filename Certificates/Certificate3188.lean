module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylFrameData
import Certificates.Kernel.LocalComp.Weyl3188

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.OmegaEight.Weyl in
theorem certificate3188 : (equivCheck = true)
    ∧ (frameCheck = true)
    ∧ (singerCheck = true) := KernelLC.W3188.cert3188

end Certificates
