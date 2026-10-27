module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.B1Basic

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section Defs

variable {W : Type} [CommGroup W] [Finite W]

@[expose] def G2Line (L₀ P : Subgroup (MulAut W)) : Prop :=
  ∃ l : Subgroup W, fixV L₀ ≤ l ∧ Nat.card ↥l = 4 * Nat.card ↥(fixV L₀) ∧
    ∀ φ ∈ P, ∀ w ∈ l, φ w ∈ l

@[expose] def G2Point (X₀ L₀ P : Subgroup (MulAut W)) : Prop :=
  ∃ A : Subgroup (MulAut W), A ≤ pCoreOf 2 P ∧ IsFFStarOffender X₀ A ∧
    (∀ B : Subgroup (MulAut W), B ≤ pCoreOf 2 P → IsFFStarOffender X₀ B → B = A) ∧
    pCoreOf 2 P ⊓ centSub (fixV A) ≤ A ∧ Nat.card ↥A = 8 ∧ rkIdx (fixV A) = 3 ∧
    ∃ c ∈ L₀, L₀ ≤ A ⊔ B1.conjAut c A

structure G2Facts (X₀ L₀ : Subgroup (MulAut W)) : Prop where
  card_X : Nat.card ↥X₀ = 12096
  rk_L : rkIdx (fixV L₀) = 6
  no_off : ∀ B : Subgroup (MulAut W), B ≤ L₀ → B ≠ ⊥ → IsElemAbelian2 B →
    Nat.card W ≤ Nat.card ↥B * Nat.card ↥(fixV B) → False
  sylow_self : ∀ S : Subgroup (MulAut W), IsSylowTwoOf S X₀ →
    X₀ ⊓ normalizer (S : Set (MulAut W)) ≤ S
  dichotomy : ∀ S P : Subgroup (MulAut W), IsSylowTwoOf S X₀ → S ≤ P → P ≤ X₀ → P ≠ X₀ →
    (∀ H : Subgroup (MulAut W), P ≤ H → H ≤ X₀ → H = P ∨ H = X₀) →
      G2Line L₀ P ∨ G2Point X₀ L₀ P

end Defs

end CFSG.Quasithin.H13.U3.GC137
