module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainT0Data
import Certificates.Kernel.OmegaEight.T0

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.OmegaEight.Chain CFSG.EvenSmallLie.OmegaEight.Stage1 in
theorem certificate3494 : (wordsCheck = true)
    ∧ (uIdxCheck = true)
    ∧ (e0Check = true)
    ∧ (t0Check = true) := KernelO8.cert3494

end Certificates

end
