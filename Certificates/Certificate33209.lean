module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwFinDefs
import Certificates.Kernel.L34Tw.Final

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.GrSLit.L34Tw CFSG.ComponentClassification.PSL3Four in
theorem certificate33209 : ∃ t ∈ RA, cosRA t = 1 ∧ t * t = 1 ∧ g₅ * t = t * g₅ ∧ g₅ * g₆ * t = t * (g₅ * g₆) ∧
    g₅ * g₆ = g₆ * g₅ ∧ t ≠ g₅ := KernelLC.L34Tw.facts33209

end Certificates
