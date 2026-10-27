module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData
import Certificates.Kernel.LocalComp.L34KLFinal

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.PSL3Four in
theorem certificate799526 : ∃ A₀ : Subgroup (Equiv.Perm (Fin 42)), A₀ ≤ S ∧ Nat.card A₀ = 9 ∧
    (∀ x ∈ R, x ^ 3 = 1 → (∀ a ∈ A₀, x * a * x⁻¹ ∈ A₀) →
      60 ≤ Nat.card (Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 42))) ⊓ S :
        Subgroup (Equiv.Perm (Fin 42))) →
      ∃ τ ∈ S, τ ^ 2 = 1 ∧ τ ≠ 1 ∧ (∀ a ∈ A₀, τ * a * τ⁻¹ = a⁻¹) ∧ x * τ = τ * x) ∧
    (∀ x ∈ R, x ∉ S → x ^ 3 = 1 →
      60 ≤ Nat.card (Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 42))) ⊓ S :
        Subgroup (Equiv.Perm (Fin 42))) →
      Nat.card (Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 42))) ⊓ S :
        Subgroup (Equiv.Perm (Fin 42))) = 60) := KernelLC.L34KL.facts799526

end Certificates
