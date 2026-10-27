module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4136Input

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W]

structure Std136 (Y : Subgroup (MulAut W)) (t : MulAut W) : Prop where
  isK : CFSG.Open.IsKGroup ↥Y
  o2 : ∀ P : Subgroup (MulAut W), P ≤ Y → (P.subgroupOf Y).Normal → IsPGroup 2 P → P = ⊥
  basic : IsBasicModule Y
  tY : t ∈ Y
  t2 : orderOf t = 2
  cost : rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3

theorem w4Lem13_6_of_std (h : ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) → ∀ (Y :
    Subgroup (MulAut W)) (t : MulAut W), Std136 Y t → ∃ L : Subgroup (MulAut W), Conc4_136W Y t
    L) : W4Lem13_6 :=
  fun W _ _ hw2 Y hK ho2 hb t htY ht2 hc => h W hw2 Y t ⟨hK, ho2, hb, htY, ht2, hc⟩

structure Ctx136 (Y : Subgroup (MulAut W)) (t : MulAut W) (L : Subgroup (MulAut W)) : Prop where
  std : Std136 Y t
  comp : IsComponentOf L Y
  Lt : ⁅L, Subgroup.zpowers t⁆ = L
  hF : ∀ p : ℕ, p.Prime → ⁅pCoreOf p Y, Subgroup.zpowers t⁆ = ⊥
  hfix : ∀ K : Subgroup (MulAut W), IsComponentOf K Y → K.map (MulAut.conj t).toMonoidHom = K

abbrev Wd (L : Subgroup (MulAut W)) : Subgroup W := commSub ⊤ L

abbrev Cd (L : Subgroup (MulAut W)) : Subgroup W := commSub ⊤ L ⊓ fixV L

noncomputable abbrev tcost (t : MulAut W) (L : Subgroup (MulAut W)) (J : Subgroup W) : ℕ :=
  E3.mQuot (commSub J (Subgroup.zpowers t) ⊔ Cd L) (Cd L)

@[expose] def Tcl (Y L : Subgroup (MulAut W)) : Prop :=
  ∀ g ∈ Y, g ∉ Subgroup.normalizer (L : Set (MulAut W)) →
    commSub (Wd L) (L.map (MulAut.conj g).toMonoidHom) = ⊥

@[expose] def PerfCentTriv (Y L : Subgroup (MulAut W)) : Prop :=
  ∀ X : Subgroup (MulAut W), X ≤ Y → ⁅X, X⁆ = X → ⁅X, L⁆ = ⊥ →
    ∀ M : Subgroup W, Cd L < M → M ≤ Wd L → StableUnder L M → commSub M X ≤ Cd L →
      commSub (Wd L) X ≤ Cd L

@[expose] def McLShape {M : Type} [CommGroup M] [Finite M] (L : Subgroup (MulAut M)) : Prop :=
  (∃ m : ℕ, IsSLn ↥L m 1 ∧ BinaryNaturalSL L ⊤ ⊥ m 1) ∨
    (∃ m : ℕ, IsSpn ↥L m 1 ∧ NatSpn L ⊤ ⊥ m 1) ∨
    (∃ m : ℕ, IsOmegaPlus ↥L m 1 ∧ NatOmegaPlus L ⊤ ⊥ m 1) ∨
    (∃ m : ℕ, IsOmegaMinus ↥L m 1 ∧ NatOmegaMinus L ⊤ ⊥ m 1) ∨
    (∃ m : ℕ, IsAlt ↥L m ∧ AlternatingNatural L ⊤ ⊥ m)

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
