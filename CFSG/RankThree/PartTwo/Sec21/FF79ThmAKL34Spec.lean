
module


public import Certificates.Certificate799525

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.KL34

open CFSG.ComponentClassification.PSL3Four

theorem l34KLSpec :
    ∃ A₀ : Subgroup (Equiv.Perm (Fin 42)), A₀ ≤ S ∧ Nat.card A₀ = 9 ∧
      (∀ x ∈ R, (∀ a ∈ A₀, x * a = a * x) → x ^ 4 = 1 → x ^ 2 = 1) ∧
      (∀ x ∈ R, x ^ 3 = 1 → (∀ a ∈ A₀, x * a * x⁻¹ ∈ A₀) →
        60 ≤ Nat.card (Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 42))) ⊓ S :
          Subgroup (Equiv.Perm (Fin 42))) →
        ∃ q ∈ S, (∀ a ∈ A₀, q * a * q⁻¹ ∈ A₀) ∧ q ^ 4 = 1 ∧ q ^ 2 ≠ 1 ∧
          x * q ^ 2 = q ^ 2 * x) :=
  Certificates.certificate799525

end CFSG.RankThree.PartTwo.Sec21.FF79.KL34
