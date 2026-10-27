module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData
import Certificates.Kernel.LocalComp.L34GrFinal

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.PSL3Four in
theorem certificate41502 : ∃ T₀ : Subgroup (Equiv.Perm (Fin 42)), T₀ ≤ S ∧ Nat.card T₀ = 64 ∧
    ∀ x ∈ S, (∀ t ∈ T₀, x * t * x⁻¹ ∈ T₀) → x ^ 3 = 1 → x ≠ 1 →
      (∀ r ∈ R, (∀ t ∈ T₀, r * t * r⁻¹ ∈ T₀) → r * x = x * r → r ^ 4 = 1 → r ^ 2 = 1) ∧
      (∀ r ∈ R, (∀ t ∈ T₀, r * t * r⁻¹ ∈ T₀) → r * x = x * r →
        ∀ r' ∈ R, (∀ t ∈ T₀, r' * t * r'⁻¹ ∈ T₀) → r' * x = x * r' →
          r ^ 2 = 1 → r' ^ 2 = 1 → r ≠ 1 → r' ≠ 1 → r ≠ r' → r * r' ≠ r' * r) ∧
      (∀ r ∈ R, (∀ t ∈ T₀, r * t * r⁻¹ ∈ T₀) → r * x = x * r → r ^ 2 = 1 → r ≠ 1 →
        ∀ t ∈ S, t * x = x * t → t * r = r * t → t = 1 ∨ t = x ∨ t = x * x) := KernelLC.L34Gr.spec

end Certificates
