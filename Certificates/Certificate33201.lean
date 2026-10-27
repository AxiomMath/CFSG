module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwFinDefs
import Certificates.Kernel.L34Tw.Final

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.GrSLit.L34Tw CFSG.ComponentClassification.GrSLit.L34Facts in
theorem certificate33201 : ∀ s ∈ RA, s * s = 1 → (cosRA s = 1 ∨ cosRA s = 2) → ∃ e₁ e₂, e₁ ∈ T0 ∧ e₂ ∈ T0 ∧
    e₁ * e₁ = 1 ∧ e₂ * e₂ = 1 ∧ e₁ ≠ 1 ∧ e₂ ≠ 1 ∧ e₂ ≠ e₁ ∧ e₁ * e₂ = e₂ * e₁ ∧
    e₁ * s = s * e₁ ∧ e₂ * s = s * e₂ := KernelLC.L34Tw.facts33201

end Certificates
