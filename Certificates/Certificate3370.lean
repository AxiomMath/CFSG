module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Data
import Certificates.Kernel.OmegaEight.Orth

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.OmegaEight.Stage1 in
theorem certificate3370 : (genCheck .plus = true)
    ∧ (genCheck .minus = true)
    ∧ (orbitCheck .plus = true)
    ∧ (orbitCheck .minus = true)
    ∧ (oCheck .plus = true)
    ∧ (oCheck .minus = true)
    ∧ (dickCheck .plus = true)
    ∧ (dickCheck .minus = true)
    ∧ (coneCheck .plus = true)
    ∧ (coneCheck .minus = true) := KernelO8.cert3370

end Certificates
