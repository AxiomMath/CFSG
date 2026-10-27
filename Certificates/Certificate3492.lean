module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainAbelData
import Certificates.Kernel.OmegaEight.Chain

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.OmegaEight.Chain CFSG.EvenSmallLie.OmegaEight.Stage1 in
theorem certificate3492 : (s0Check .plus = true)
    ∧ (s0Check .minus = true)
    ∧ (abelCheck .plus = true)
    ∧ (abelCheck .minus = true) := KernelO8.cert3492

end Certificates

end
