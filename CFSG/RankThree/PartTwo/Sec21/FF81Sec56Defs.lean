module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open Matrix

def KF_Sp6ShortRootCen : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X), StatedClassicalModel ↥L .PSp 3 2 1 →
    ∀ b₁ b₂ b₃ : X, b₁ ∈ L → b₂ ∈ L → b₃ ∈ L → IsElemAb 3 3 (Subgroup.closure {b₁, b₂, b₃}) →
    L ⊓ CenS (Subgroup.closure {b₁, b₂, b₃}) = Subgroup.closure {b₁, b₂, b₃} →
    (∀ n ∈ L, n ∈ Nor (Subgroup.closure {b₁, b₂, b₃}) → ∀ x ∈ ({b₁, b₂, b₃} : Set X),
      n * x * n⁻¹ ∈ ({b₁, b₁⁻¹, b₂, b₂⁻¹, b₃, b₃⁻¹} : Set X)) →
    ∀ s ∈ L, orderOf s = 2 → s * b₁ = b₁ * s → s * (b₂ * b₃) = b₂ * b₃ * s →
      s * (b₂ * b₃ ^ 2) * s⁻¹ = (b₂ * b₃ ^ 2)⁻¹ →
      (∀ l ∈ L ⊓ Cen s, l ^ 3 = 1 →
        ∃ c ∈ L ⊓ Cen s, c * l * c⁻¹ ∈ Subgroup.closure {b₁, b₂ * b₃}) ∧
      (∀ Y : Subgroup X, Y ≤ L ⊓ Cen s → L ⊓ Cen s ≤ Nor Y → Nat.Coprime (Nat.card Y) 3 →
        Nat.card Y ≤ 128) ∧
      ¬ 5 ∣ Nat.card ↥(L ⊓ Cen s)

def KF_Sp4CenGL6 : Prop :=
  ∀ (Y : Subgroup (GL (Fin 6) (ZMod 2))) (u : GL (Fin 6) (ZMod 2))
    (φ : Equiv.Perm (Fin 6) →* GL (Fin 6) (ZMod 2)),
    orderOf u = 3 →
    16 ≤ Nat.card {v : Fin 6 → ZMod 2 // (u : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ v = v} →
    u ∈ Y → Y ≤ Subgroup.centralizer {u} → (∀ σ, φ σ ∈ Y) →
    φ (Equiv.swap 0 1 * Equiv.swap 1 2) ≠ 1 →
    Y = φ.range ⊔ Subgroup.zpowers u ∨
      (Nat.card Y = 60480 ∧ ∃ f ∈ Y, ∃ x ∈ Y, orderOf f = 5 ∧ orderOf x = 3 ∧
        x ∉ Subgroup.zpowers u ∧ f * x = x * f)

end CFSG.RankThree.PartTwo.Sec21.FF81
