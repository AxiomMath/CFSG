module

public import Certificates.Data.OmegaS107
public import Certificates.Data.OmegaTypesFacts

public section

namespace Certificates.OmegaS107

open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.GH74.KGroups Certificates.OmegaF1051

local notation "P45" => Equiv.Perm (Fin 45)

@[expose] def Q0 : Subgroup P45 := Subgroup.closure {gq1 (), gq2 (), gq3 (), gq4 ()}

structure M107 (T B2 : Subgroup P45) (y2 : P45) : Prop where
  le : B2 ≤ T
  comm : ∀ a ∈ B2, ∀ b ∈ B2, a * b = b * a
  sq : ∀ a ∈ B2, a * a = 1
  card : Nat.card B2 = 16
  normal : ∀ g ∈ T, ∀ b ∈ B2, g * b * g⁻¹ ∈ B2
  y2_mem : y2 ∈ B2
  y2_out : y2 ∉ QT0.originalSubgroup
  y2_inv : Certificates.OmegaTypes.InvC 1440 y2
  mem_B2 : ∀ b : P45, b ∈ B2 ↔
    (b ∈ Q0 ∧ b * y2 = y2 * b) ∨ ∃ c ∈ Q0, c * y2 = y2 * c ∧ c * y2 = b
  normal_elem : ∀ X : Subgroup P45, X ≤ T → (∀ a ∈ X, ∀ b ∈ X, a * b = b * a) →
    (∀ a ∈ X, a * a = 1) → Nat.card X = 16 → (∀ g ∈ T, ∀ x ∈ X, g * x * g⁻¹ ∈ X) →
      ¬ X ≤ QT0.originalSubgroup → X = B2
  meet : ∀ X : Subgroup P45, X ≤ T → (∀ a ∈ X, ∀ b ∈ X, a * b = b * a) →
    (∀ a ∈ X, a * a = 1) → Nat.card X = 16 → ¬ X ≤ QT0.originalSubgroup →
      ∃ y ∈ X, y ∈ B2 ∧ y ∉ QT0.originalSubgroup

structure Facts : Prop where
  q0_le : Q0 ≤ QT0.originalSubgroup
  q0_card : Nat.card Q0 = 32
  model : ∀ T : Subgroup P45, QT0.originalSubgroup ≤ T → T ≤ QA45.originalSubgroup →
    IsPGroup 2 T → ∀ w ∈ T, w ∉ QT0.originalSubgroup → ∃ B2 y2, M107 T B2 y2

end Certificates.OmegaS107

end
