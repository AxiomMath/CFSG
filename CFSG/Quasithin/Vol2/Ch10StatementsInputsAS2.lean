module

public import CFSG.Quasithin.Background.B4Models
public import CFSG.Quasithin.Background.Basic
public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.Quasithin.ASInputs

open CFSG.Open
open scoped IsMulCommutative

@[expose] def AS_B_4_8_four : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ Gm : Subgroup (MulAut V), Nonempty (↥Gm ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) →
    (∀ A B : Subgroup V, (∀ g ∈ Gm, ∀ a ∈ A, g a ∈ A) → (∀ g ∈ Gm, ∀ b ∈ B, g b ∈ B) →
      A ⊓ B = ⊥ → A ⊔ B = ⊤ → A = ⊥ ∨ B = ⊥) →
    (∃ W₁ W₂ : Subgroup V, W₁ ≤ W₂ ∧ W₁ ≤ fixV Gm ∧ commV Gm ≤ W₂ ∧
      BinaryNaturalSL Gm W₂ W₁ 3 1) →
      Nat.card V = 2 ^ 3 ∨ Nat.card V = 2 ^ 4

@[expose] def AS_I_1_6_one : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L W : Subgroup G), L ≤ Subgroup.normalizer (W : Set G) →
    IsElemAbelian 2 W → W = ⁅W, L⁆ →
    (∃ _ : IsMulCommutative ↥W, AlternatingNatural (V := ↥W) (autOn L W) ⊤
      ((Subgroup.centralizer (L : Set G)).subgroupOf W) 5) →
      W ⊓ Subgroup.centralizer (L : Set G) = ⊥

section Transvections

variable {V : Type*} [CommGroup V]

@[expose] def transvGroup (Gm : Subgroup (MulAut V)) (X : Subgroup V) : Subgroup (MulAut V) :=
  Subgroup.closure {g | g ∈ Gm ∧ ∀ v : V, g v * v⁻¹ ∈ X}

abbrev g31V (Δ : Set (Subgroup V)) : Subgroup V :=
  ⨆ X ∈ Δ, X

abbrev g31G (Gm : Subgroup (MulAut V)) (Δ : Set (Subgroup V)) : Subgroup (MulAut V) :=
  ⨆ X ∈ Δ, transvGroup Gm X

end Transvections

end CFSG.Quasithin.ASInputs
