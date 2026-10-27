module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData
import Certificates.Kernel.LocalComp.L34CeFinal

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.PSL3Four in
theorem certificate295200 : ∃ A₀ : Subgroup (Equiv.Perm (Fin 42)), A₀ ≤ CFSG.ComponentClassification.PSL3Four.S ∧ Nat.card A₀ = 9 ∧
    ∃ β ∈ R, β ^ 2 = 1 ∧ β ≠ 1 ∧ (∀ a ∈ A₀, β * a = a * β) ∧
      (∀ x ∈ R, (∀ a ∈ A₀, x * a = a * x) → ∃ c ∈ A₀, x = c ∨ x = c * β) ∧
      (∀ y ∈ R, (∀ a ∈ A₀, y * a * y⁻¹ ∈ A₀) → y * β = β * y) := KernelLC.L34Ce.spec

end Certificates
