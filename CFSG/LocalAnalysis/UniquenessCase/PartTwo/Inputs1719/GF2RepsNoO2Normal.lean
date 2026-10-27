module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2Reps417Tits

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)

@[expose] def W4Lem4_17TrialityD4N : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ Y L T : Subgroup (MulAut W), ∀ n : ℕ,
      L ≤ Y → T ≤ Y → L ⊔ T = Y →
      IsComponentOf L Y →
      IsSylowIn 2 T Y →
      O2Trivial Y →
      fixV T ≠ fixV Y →
      T ≤ Subgroup.normalizer (L : Set (MulAut W)) →
      Is3D4 ↥L n →
      bParam L Y ≤ 4 * n

theorem bParam_le_of_noO2_of_normal {P : ∀ (X : Type) [Group X], Prop}
    (hP : ∀ {X X' : Type} [Group X] [Group X'], (X ≃* X') → P X → P X') {B : ℕ}
    (h : ∀ (U : Type) [CommGroup U] [Finite U], (∀ u : U, u ^ 2 = 1) →
      ∀ Y L T : Subgroup (MulAut U), L ⊔ T = Y → IsComponentOf L Y →
        IsSylowIn 2 T Y → O2Trivial Y → fixV T ≠ fixV Y →
        T ≤ Subgroup.normalizer (L : Set (MulAut U)) → P ↥L → bParam L Y ≤ B)
    {W : Type} [CommGroup W] [Finite W] (hw : ∀ w : W, w ^ 2 = 1)
    {Y L T : Subgroup (MulAut W)} (hLY : L ≤ Y) (hTY : T ≤ Y) (hLT : L ⊔ T = Y)
    (hcomp : IsComponentOf L Y) (hsyl : IsSylowIn 2 T Y) (hfix : fixV T ≠ fixV Y)
    (hodd : Odd (Nat.card (Subgroup.center ↥L)))
    (hTN : T ≤ Subgroup.normalizer (L : Set (MulAut W))) (hPL : P ↥L) :
    bParam L Y ≤ B := by
  let S := noO2NormalSetup hw hLY hTY hLT hcomp hsyl hfix hodd
  have hTbN : S.Tb ≤ Subgroup.normalizer (S.Lb : Set (MulAut S.U)) :=
    CFSG.CGT.PushingUpLit.BHS.autSub_le_normalizer (E := L) (A := T) (U := S.U) hTN
  exact S.hb.trans (h ↥S.U S.hwU S.Yb S.Lb S.Tb S.hsupb S.hcompb S.hsylb S.hO2b
    S.hfixb hTbN (hP S.e hPL))

theorem bParam_le_two_of_isTits_of_normal
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y L T : Subgroup (MulAut W)} (hLY : L ≤ Y) (hTY : T ≤ Y) (hLT : L ⊔ T = Y)
    (hcomp : IsComponentOf L Y) (hsyl : IsSylowIn 2 T Y) (hfix : fixV T ≠ fixV Y)
    (hodd : Odd (Nat.card (Subgroup.center ↥L)))
    (hTN : T ≤ Subgroup.normalizer (L : Set (MulAut W))) (hTits : IsTits ↥L) :
    bParam L Y ≤ 2 := by
  refine bParam_le_of_noO2_of_normal (P := fun X _ => IsTits X)
    (hP := fun {X X'} _ _ e hh => IsTits.of_mulEquiv e hh) (B := 2) ?_
    hW hLY hTY hLT hcomp hsyl hfix hodd hTN hTits
  intro U _ _ hw Y L T hLT hcomp hsyl hO2 hfix hTN hPL
  exact bParam_le_two_of_isTits_of_le_normalizer hw hLT hcomp hsyl hO2 hfix hTN hPL

@[expose] def W4Lem4_17TwoF4N : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ Y L T : Subgroup (MulAut W), ∀ n : ℕ,
      L ≤ Y → T ≤ Y → L ⊔ T = Y →
      IsComponentOf L Y →
      IsSylowIn 2 T Y →
      fixV T ≠ fixV Y →
      Odd (Nat.card (Subgroup.center ↥L)) →
      T ≤ Subgroup.normalizer (L : Set (MulAut W)) →
      Is2F4 n ↥L →
      bParam L Y ≤ 2 * n

theorem bParam_le_two_mul_of_is2F4_of_normal (h2F4 : W4Lem4_17TwoF4N)
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y L T : Subgroup (MulAut W)} {n : ℕ} (hLY : L ≤ Y) (hTY : T ≤ Y) (hLT : L ⊔ T = Y)
    (hcomp : IsComponentOf L Y) (hsyl : IsSylowIn 2 T Y) (hfix : fixV T ≠ fixV Y)
    (hodd : Odd (Nat.card (Subgroup.center ↥L)))
    (hTN : T ≤ Subgroup.normalizer (L : Set (MulAut W)))
    (hshape : Is2F4 n ↥L) : bParam L Y ≤ 2 * n :=
  h2F4 W hW Y L T n hLY hTY hLT hcomp hsyl hfix hodd hTN hshape

theorem bParam_le_four_mul_of_is3D4_of_normal
    (h3D4 : W4Lem4_17TrialityD4N)
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y L T : Subgroup (MulAut W)} {n : ℕ} (hLY : L ≤ Y) (hTY : T ≤ Y) (hLT : L ⊔ T = Y)
    (hcomp : IsComponentOf L Y) (hsyl : IsSylowIn 2 T Y) (hfix : fixV T ≠ fixV Y)
    (hodd : Odd (Nat.card (Subgroup.center ↥L)))
    (hTN : T ≤ Subgroup.normalizer (L : Set (MulAut W)))
    (h3 : CFSG.LocalAnalysis.UniquenessCase.UC22.Is3D4 ↥L n) : bParam L Y ≤ 4 * n := by
  refine bParam_le_of_noO2_of_normal
    (P := fun X _ => CFSG.LocalAnalysis.UniquenessCase.UC22.Is3D4 X n)
    (hP := fun {X X'} _ _ e hh => LieModel.of_mulEquiv e hh) (B := 4 * n) ?_
    hW hLY hTY hLT hcomp hsyl hfix hodd hTN h3
  intro U _ _ hw Y L T hLT hcomp hsyl hO2 hfix hTN hPL
  exact h3D4 U hw Y L T n (hLT ▸ le_sup_left) (hLT ▸ le_sup_right) hLT hcomp hsyl hO2
    hfix hTN hPL

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
