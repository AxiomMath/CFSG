
module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData
import Certificates.Kernel.LocalComp.L34KLFinal

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.PSL3Four in
theorem certificate799525 : ∃ A₀ : Subgroup (Equiv.Perm (Fin 42)), A₀ ≤ S ∧ Nat.card A₀ = 9 ∧
    (∀ x ∈ R, (∀ a ∈ A₀, x * a = a * x) → x ^ 4 = 1 → x ^ 2 = 1) ∧
    (∀ x ∈ R, x ^ 3 = 1 → (∀ a ∈ A₀, x * a * x⁻¹ ∈ A₀) →
      60 ≤ Nat.card (Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 42))) ⊓ S :
        Subgroup (Equiv.Perm (Fin 42))) →
      ∃ q ∈ S, (∀ a ∈ A₀, q * a * q⁻¹ ∈ A₀) ∧ q ^ 4 = 1 ∧ q ^ 2 ≠ 1 ∧ x * q ^ 2 = q ^ 2 * x) := KernelLC.L34KL.facts799525

end Certificates
