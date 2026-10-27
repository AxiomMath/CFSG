module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainZ4Data
import Certificates.Kernel.OmegaEight.Chain4Eval

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.OmegaEight.Chain CFSG.EvenSmallLie.OmegaEight.Stage1 in
theorem certificate3493 : (relCheck4 .plus = true)
    ∧ (relCheck4 .minus = true)
    ∧ (kCheck = true)
    ∧ (sqCheck = true)
    ∧ (centerCheck .plus = true)
    ∧ (centerCheck .minus = true) := KernelO8.cert3493

end Certificates
