module

public import Certificates.Certificate799526

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.KL35

open CFSG.ComponentClassification.PSL3Four

theorem l35KLSpec :
    ∃ A₀ : Subgroup (Equiv.Perm (Fin 42)), A₀ ≤ S ∧ Nat.card A₀ = 9 ∧
      (∀ x ∈ R, x ^ 3 = 1 → (∀ a ∈ A₀, x * a * x⁻¹ ∈ A₀) →
        60 ≤ Nat.card (Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 42))) ⊓ S :
          Subgroup (Equiv.Perm (Fin 42))) →
        ∃ τ ∈ S, τ ^ 2 = 1 ∧ τ ≠ 1 ∧ (∀ a ∈ A₀, τ * a * τ⁻¹ = a⁻¹) ∧ x * τ = τ * x) ∧
      (∀ x ∈ R, x ∉ S → x ^ 3 = 1 →
        60 ≤ Nat.card (Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 42))) ⊓ S :
          Subgroup (Equiv.Perm (Fin 42))) →
        Nat.card (Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 42))) ⊓ S :
          Subgroup (Equiv.Perm (Fin 42))) = 60) :=
  Certificates.certificate799526

end CFSG.RankThree.PartTwo.Sec21.FF79.KL35
