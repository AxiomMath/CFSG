module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

def KF_Sp6Cls : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (M : Subgroup X), StatedClassicalModel ↥M .PSp 3 2 1 →
    (∀ g ∈ M, orderOf g = 3 → Nat.card ↥(M ⊓ Cen g) = 2160 ∨ Nat.card ↥(M ⊓ Cen g) = 648 ∨
      Nat.card ↥(M ⊓ Cen g) = 108) ∧
    (∀ g ∈ M, ∀ h ∈ M, orderOf g = 3 → orderOf h = 3 →
      Nat.card ↥(M ⊓ Cen g) = Nat.card ↥(M ⊓ Cen h) → ∃ m ∈ M, m * g * m⁻¹ = h) ∧
    (∀ s ∈ M, orderOf s = 2 → 5 ∣ Nat.card ↥(M ⊓ Cen s) → ∀ g ∈ M ⊓ Cen s, orderOf g = 3 →
      Nat.card ↥(M ⊓ Cen g) ≠ 648) ∧
    (∀ τ ∈ M, orderOf τ = 2 → ∃ γ ∈ M ⊓ Cen τ, orderOf γ = 3 ∧
      (Nat.card ↥(M ⊓ Cen γ) = 108 ∨ Nat.card ↥(M ⊓ Cen γ) = 2160) ∧
      ∃ k ∈ M ⊓ Cen τ, orderOf k = 2 ∧ k * γ * k⁻¹ = γ⁻¹) ∧
    ∀ s ∈ M, orderOf s = 2 → 5 ∣ Nat.card ↥(M ⊓ Cen s) →
      Nat.card ↥(M ⊓ Cen s) = 23040 ∧ ∃ T : Subgroup X, T ≤ M ⊓ Cen s ∧ Nat.card T = 512 ∧
        s ∈ T ∧ ∀ y ∈ T, (∀ t ∈ T, y * t = t * y) → orderOf y = 2 →
          5 ∣ Nat.card ↥(M ⊓ Cen y) → y = s

def KF_Sp6ShortRoot3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X), StatedClassicalModel ↥L .PSp 3 2 1 →
    ∀ b₁ b₂ b₃ : X, b₁ ∈ L → b₂ ∈ L → b₃ ∈ L → IsElemAb 3 3 (Subgroup.closure {b₁, b₂, b₃}) →
    L ⊓ CenS (Subgroup.closure {b₁, b₂, b₃}) = Subgroup.closure {b₁, b₂, b₃} →
    (∀ n ∈ L, n ∈ Nor (Subgroup.closure {b₁, b₂, b₃}) → ∀ x ∈ ({b₁, b₂, b₃} : Set X),
      n * x * n⁻¹ ∈ ({b₁, b₁⁻¹, b₂, b₂⁻¹, b₃, b₃⁻¹} : Set X)) →
    ∀ s ∈ L, orderOf s = 2 → s * b₁ = b₁ * s → s * (b₂ * b₃) = b₂ * b₃ * s →
      s * (b₂ * b₃ ^ 2) * s⁻¹ = (b₂ * b₃ ^ 2)⁻¹ →
      Nat.card ↥(L ⊓ Cen (b₂ * b₃ ^ 2)) = 108

end CFSG.RankThree.PartTwo.Sec21.FF81
