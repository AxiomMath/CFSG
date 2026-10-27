module

public import CFSG.RankThree.PartTwo.Sec21.FF81Defs

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open Matrix

def KF_Sp6GL6Cen : Prop :=
  ∀ (X : Subgroup (GL (Fin 6) (ZMod 2))) (u : GL (Fin 6) (ZMod 2))
    (φ : Equiv.Perm (Fin 6) →* GL (Fin 6) (ZMod 2)),
    orderOf u = 3 →
    16 ≤ Nat.card {v : Fin 6 → ZMod 2 // (u : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ v = v} →
    φ (Equiv.swap 0 1 * Equiv.swap 1 2) ≠ 1 →
    X ⊓ Subgroup.centralizer {u} = φ.range ⊔ Subgroup.zpowers u → 81 ∣ Nat.card X →
    Nat.card X = 1451520 ∧
      X = Subgroup.closure {g | g ∈ X ∧ ((g : Matrix (Fin 6) (Fin 6) (ZMod 2)) - 1).rank = 1} ∧
      ∀ W : Submodule (ZMod 2) (Fin 6 → ZMod 2),
        (∀ g ∈ X, ∀ w ∈ W, (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ w ∈ W) → W = ⊥ ∨ W = ⊤

abbrev M₅₇ {G : Type} [Group G] (b b₁ b₂ b₃ s₀ : G) : Subgroup G :=
  OUp 3 (CenS (Subgroup.closure {b₂, b₃})) ⊔
    (CenS (Subgroup.closure {β' b₂ b₃, s₀}) ⊓ Nor (Subgroup.closure {b, b₁, b₂ * b₃}))

def FF81_5_7b : Prop :=
  KF_HoltThm1 →
  ∀ (G : Type) [Group G] [Finite G] (b : G) (L B : Subgroup G) (b₁ b₂ b₃ t₀ s₀ : G),
    FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀ → ControlsFusionIn B → FF81Conc5_2_6 b b₁ b₂ b₃ s₀ →
    StatedClassicalModel (M₅₇ b b₁ b₂ b₃ s₀) .PSp 3 2 1 →
    setMul (Op 2 (Cen s₀)) (M₅₇ b b₁ b₂ b₃ s₀) = Cen s₀ →
    Subgroup.zpowers (β' b₂ b₃) ∉ ConjLines B b →
    Subgroup.zpowers (β' b₂ b₃) ⊔ M₅₇ b b₁ b₂ b₃ s₀ = Cen (β' b₂ b₃)

end CFSG.RankThree.PartTwo.Sec21.FF81
