module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData
import Certificates.Kernel.LocalComp.L34F9460

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.PSL3Four in
theorem certificate9460 : ∃ T₀ : Subgroup (Equiv.Perm (Fin 42)), T₀ ≤ S ∧ Nat.card T₀ = 9 ∧
    ∀ x ∈ R, x ^ 3 = 1 → x ∉ S → (∀ t ∈ T₀, x * t * x⁻¹ ∈ T₀) →
      ∃ c ∈ S, c * x = x * c ∧ ∃ t ∈ T₀, c * t * c⁻¹ ∉ T₀ :=
  KernelLC.L34F946.spec9460

end Certificates
