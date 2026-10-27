module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

def KF_Sp6ShortRoot : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X), StatedClassicalModel ↥L .PSp 3 2 1 →
    ∀ b₁ b₂ b₃ : X, b₁ ∈ L → b₂ ∈ L → b₃ ∈ L → IsElemAb 3 3 (Subgroup.closure {b₁, b₂, b₃}) →
    L ⊓ CenS (Subgroup.closure {b₁, b₂, b₃}) = Subgroup.closure {b₁, b₂, b₃} →
    (∀ n ∈ L, n ∈ Nor (Subgroup.closure {b₁, b₂, b₃}) → ∀ x ∈ ({b₁, b₂, b₃} : Set X),
      n * x * n⁻¹ ∈ ({b₁, b₁⁻¹, b₂, b₂⁻¹, b₃, b₃⁻¹} : Set X)) →
    ∀ s ∈ L, orderOf s = 2 → s * b₁ = b₁ * s → s * (b₂ * b₃) = b₂ * b₃ * s →
      s * (b₂ * b₃ ^ 2) * s⁻¹ = (b₂ * b₃ ^ 2)⁻¹ →
      (∃ v ∈ L ⊓ Cen s ⊓ Cen (b₁ * (b₂ * b₃)), v ^ 4 = 1 ∧ v ≠ 1 ∧ v ≠ s) ∧
      (∃ v ∈ L ⊓ Cen s ⊓ Cen b₁, v * v = 1 ∧
        (∀ g ∈ L ⊓ Cen s ⊓ Cen b₁, g * v * g⁻¹ * v = v * (g * v * g⁻¹)) ∧ v ≠ 1 ∧ v ≠ s) ∧
      ∀ R : Subgroup X, R ≤ L ⊓ Cen s → IsPGroup 2 R → L ⊓ Cen s ≤ Nor R → s ∈ R →
        (Nat.card R = 2 ∧ Nat.card ↥(R ⊓ Cen b₁) = 2 ∧ Nat.card ↥(R ⊓ Cen (b₁ * (b₂ * b₃))) = 2 ∧
          Nat.card ↥(R ⊓ Cen (b₂ * b₃)) = 2) ∨
        (Nat.card R = 8 ∧ Nat.card ↥(R ⊓ Cen b₁) = 8 ∧ Nat.card ↥(R ⊓ Cen (b₁ * (b₂ * b₃))) = 2 ∧
          Nat.card ↥(R ⊓ Cen (b₂ * b₃)) = 2 ∧
          ∀ v ∈ L ⊓ Cen s ⊓ Cen (b₁ * (b₂ * b₃)), v ^ 4 = 1 → v ∈ CenS R) ∨
        (Nat.card R = 32 ∧ Nat.card ↥(R ⊓ Cen b₁) = 2 ∧ Nat.card ↥(R ⊓ Cen (b₁ * (b₂ * b₃))) = 8 ∧
          Nat.card ↥(R ⊓ Cen (b₂ * b₃)) = 2 ∧
          ∀ v ∈ L ⊓ Cen s ⊓ Cen b₁, v * v = 1 →
            (∀ g ∈ L ⊓ Cen s ⊓ Cen b₁, g * v * g⁻¹ * v = v * (g * v * g⁻¹)) → v ∈ CenS R) ∨
        (Nat.card R = 128 ∧ Nat.card ↥(R ⊓ Cen b₁) = 8 ∧
          Nat.card ↥(R ⊓ Cen (b₁ * (b₂ * b₃))) = 8 ∧ Nat.card ↥(R ⊓ Cen (b₂ * b₃)) = 2 ∧
          IsElemAb 2 3 (R ⊓ Cen b₁) ∧ R ⊓ Cen (b₁ * (b₂ * b₃)) ≤ CenS (R ⊓ Cen b₁) ∧
          R ⊓ Cen (b₁⁻¹ * (b₂ * b₃)) ≤ CenS (R ⊓ Cen b₁) ∧
          R ⊓ Cen (b₁⁻¹ * (b₂ * b₃)) ≤ CenS (R ⊓ Cen (b₁ * (b₂ * b₃))) ∧
          Nat.card ↥(R ⊓ Cen (b₁ * (b₂ * b₃)) ⊔ R ⊓ Cen (b₁⁻¹ * (b₂ * b₃))) = 32 ∧
          (∀ q ∈ R ⊓ Cen (b₁ * (b₂ * b₃)) ⊔ R ⊓ Cen (b₁⁻¹ * (b₂ * b₃)),
            (∀ y ∈ R ⊓ Cen (b₁ * (b₂ * b₃)) ⊔ R ⊓ Cen (b₁⁻¹ * (b₂ * b₃)), q * y = y * q) →
              q = 1 ∨ q = s) ∧
          (∀ q ∈ R ⊓ Cen (b₁ * (b₂ * b₃)) ⊔ R ⊓ Cen (b₁⁻¹ * (b₂ * b₃)), q * q = 1 ∨ q * q = s) ∧
          (∀ q ∈ R ⊓ Cen (b₁ * (b₂ * b₃)) ⊔ R ⊓ Cen (b₁⁻¹ * (b₂ * b₃)),
            ∀ y ∈ R ⊓ Cen (b₁ * (b₂ * b₃)) ⊔ R ⊓ Cen (b₁⁻¹ * (b₂ * b₃)),
              q * y * q⁻¹ * y⁻¹ = 1 ∨ q * y * q⁻¹ * y⁻¹ = s) ∧
          ∃ A : Subgroup X, A ≤ R ⊓ Cen (b₁ * (b₂ * b₃)) ⊔ R ⊓ Cen (b₁⁻¹ * (b₂ * b₃)) ∧
            IsElemAb 2 3 A ∧ s ∈ A)

end CFSG.RankThree.PartTwo.Sec21.FF81
