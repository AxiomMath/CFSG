module

public import CFSG.RankThree.PartTwo.Sec21.FF81Defs

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.F4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF79
  CFSG.RankThree.PartTwo.Sec21.FF81
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.Blueprint (ChevalleyExceptionalModel)

def KF_F4Local' : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Y : Subgroup X), ChevalleyExceptionalModel Y .F4 2 1 →
    (∀ z ∈ Y, (∀ y ∈ Y, z * y = y * z) → z = 1) ∧
    (∀ g ∈ Nor Y, (¬ ∃ y ∈ Y, ∀ x ∈ Y, g * x * g⁻¹ = y * x * y⁻¹) →
      (∃ y ∈ Y, ∀ x ∈ Y, (g * y) ^ 2 * x = x * (g * y) ^ 2) ∧
      ∀ u ∈ Y, ∀ v ∈ Y, orderOf u = 2 → orderOf v = 2 →
        Nat.card ↥(Y ⊓ Cen u) = 2 ^ 24 * 3 ^ 4 * 5 * 7 →
        Nat.card ↥(Y ⊓ Cen v) = 2 ^ 24 * 3 ^ 4 * 5 * 7 →
        ∃ y ∈ Y, y * u * y⁻¹ = v ∨ y * (g * u * g⁻¹) * y⁻¹ = v) ∧
    (∀ x ∈ Y, orderOf x = 3 → 3 ^ 6 ∣ Nat.card ↥(Y ⊓ Cen x) ∨
      Nat.card ↥(Y ⊓ Cen x) = 2 ^ 9 * 3 ^ 5 * 5 * 7) ∧
    (∀ U : Subgroup X, IsSylowOf 2 U Y → Nat.card ↥(Subgroup.center ↥U) = 4 ∧
      U = Subgroup.closure {u | u ∈ U ∧ orderOf u = 2 ∧
        Nat.card ↥(Y ⊓ Cen u) = 2 ^ 24 * 3 ^ 4 * 5 * 7}) ∧
    (∀ B : Subgroup X, B ≤ Y → IsElemAb 3 4 B → Y ⊓ CenS B = B → ∀ x ∈ Y, orderOf x = 3 →
      ¬ 3 ^ 6 ∣ Nat.card ↥(Y ⊓ Cen x) →
      {D : Subgroup X | D ≤ B ∧ ∃ y ∈ Y, conjBy y (Subgroup.zpowers x) = D}.ncard ≤ 12 ∧
        ∃ y ∈ Y, y * x * y⁻¹ ∈ B) ∧
    (∀ Q : Subgroup X, IsSylowOf 3 Q Y → ∀ B₁ B₂ : Subgroup X, B₁ ≤ Q → B₂ ≤ Q →
      IsElemAb 3 4 B₁ → IsElemAb 3 4 B₂ → B₁ = B₂) ∧
    (∀ t ∈ Y, orderOf t = 2 → ∀ x ∈ Y, orderOf x = 3 → ¬ 3 ^ 6 ∣ Nat.card ↥(Y ⊓ Cen x) →
      ∃ y ∈ Y, y * x * y⁻¹ ∈ Cen t) ∧
    (∀ x ∈ Y, orderOf x = 3 → ∀ K : Subgroup X, K ≤ Y → Subgroup.zpowers x ⊔ K = Y ⊓ Cen x →
      StatedClassicalModel K .PSp 3 2 1 → ∀ x₁ ∈ K, ∀ x₂ ∈ K, (∃ y ∈ Y, y * x * y⁻¹ = x₁) →
      (∃ y ∈ Y, y * x * y⁻¹ = x₂) → ∃ k ∈ K, k * x₁ * k⁻¹ = x₂) ∧
    (∀ U : Subgroup X, IsSylowOf 2 U Y → ∀ z₁ ∈ U, ∀ z₂ ∈ U, (∀ u ∈ U, z₁ * u = u * z₁) →
      (∀ u ∈ U, z₂ * u = u * z₂) → (∃ y ∈ Y, y * z₁ * y⁻¹ = z₂) → z₁ = z₂) ∧
    ∀ τ : X, orderOf τ = 2 → τ ∈ Nor Y → (¬ ∃ y ∈ Y, ∀ x ∈ Y, τ * x * τ⁻¹ = y * x * y⁻¹) →
      ∀ R : Subgroup X, R ≤ Y ⊓ Cen τ → IsPGroup 2 R → Y ⊓ Cen τ ≤ Nor R → R = ⊥

end CFSG.RankThree.PartTwo.Sec21.FF81.F4
