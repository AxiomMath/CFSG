module

public import CFSG.Quasithin.Background.D36GluedReduction
public import CFSG.Quasithin.Background.D36GluedL24Model

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

@[expose] def GluedL24 {W : Type} [CommGroup W] (L : Subgroup (MulAut W)) (VT U : Subgroup W) :
    Prop :=
  BinaryNaturalSL (autSub L VT) (U.subgroupOf VT) (U.subgroupOf VT ⊓ fixV (autSub L VT)) 2 2

@[expose] def GluedL3 {W : Type} [CommGroup W] (L : Subgroup (MulAut W)) (VT U : Subgroup W) :
    Prop :=
  BinaryNaturalSL (autSub L VT) (U.subgroupOf VT) (U.subgroupOf VT ⊓ fixV (autSub L VT)) 3 1

@[expose] def D36GluedDiagL3 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W)
    (t : MulAut W), D36Norm M Mp T L V t →
    ¬ IsIntDirect (commSub (orbSup T V) L) ((commSub (orbSup T V) L).map t.toMonoidHom)
      (orbSup T V) →
    ∀ A : Subgroup (MulAut W), A ≤ T → autSub A (orbSup T V) ∈ QhatStar (autSub T (orbSup T V)) →
      ¬ A ≤ stabSub (commSub (orbSup T V) L) →
      GluedDiag L A (orbSup T V) (commSub (orbSup T V) L) →
      GluedL3 L (orbSup T V) (commSub (orbSup T V) L) →
      CubicBound (autSub (Mp ⊔ T) (orbSup T V)) (autSub A (orbSup T V))
        ((commSub (orbSup T V) L).subgroupOf (orbSup T V))
        (((commSub (orbSup T V) L).map t.toMonoidHom).subgroupOf (orbSup T V)) →
      DiagShape (autSub A (orbSup T V)) (autSub L (orbSup T V))
        ((commSub (orbSup T V) L).subgroupOf (orbSup T V))
        (((commSub (orbSup T V) L).map t.toMonoidHom).subgroupOf (orbSup T V)) → False

@[expose] def D36GluedDiagOther : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W)
    (t : MulAut W), D36Norm M Mp T L V t →
    ¬ IsIntDirect (commSub (orbSup T V) L) ((commSub (orbSup T V) L).map t.toMonoidHom)
      (orbSup T V) →
    ∀ A : Subgroup (MulAut W), A ≤ T → autSub A (orbSup T V) ∈ QhatStar (autSub T (orbSup T V)) →
      ¬ A ≤ stabSub (commSub (orbSup T V) L) →
      GluedDiag L A (orbSup T V) (commSub (orbSup T V) L) →
      ¬ GluedL24 L (orbSup T V) (commSub (orbSup T V) L) →
      ¬ GluedL3 L (orbSup T V) (commSub (orbSup T V) L) →
      CubicBound (autSub (Mp ⊔ T) (orbSup T V)) (autSub A (orbSup T V))
        ((commSub (orbSup T V) L).subgroupOf (orbSup T V))
        (((commSub (orbSup T V) L).map t.toMonoidHom).subgroupOf (orbSup T V)) →
      DiagShape (autSub A (orbSup T V)) (autSub L (orbSup T V))
        ((commSub (orbSup T V) L).subgroupOf (orbSup T V))
        (((commSub (orbSup T V) L).map t.toMonoidHom).subgroupOf (orbSup T V)) → False

theorem d36GluedDiag_of_cases (hL38 : D3L38) (hL3 : D36GluedDiagL3) (hO : D36GluedDiagOther) :
    D36GluedDiag := by
  intro W _ _ M Mp T L V t n hd A hA hQ hAU hdiag hcub hshape
  by_cases hn24 : GluedL24 L (orbSup T V) (commSub (orbSup T V) L)
  · exact (d36_gluedSwap hL38 n hA hQ hAU).false_of_L24 (d36_exp_VT n) (d36_L_le_X n)
      (d36_L_fix_Ut' hL38 n) hdiag hn24 l24NaturalSection_holds
  by_cases hn3 : GluedL3 L (orbSup T V) (commSub (orbSup T V) L)
  · exact hL3 W M Mp T L V t n hd A hA hQ hAU hdiag hn3 hcub hshape
  · exact hO W M Mp T L V t n hd A hA hQ hAU hdiag hn24 hn3 hcub hshape

theorem d36ActsGlued_of_residual (hL38 : D3L38) (hL3 : D36GluedDiagL3) (hO : D36GluedDiagOther)
    (hN : D36GluedNonDiag) : D36ActsGlued :=
  d36ActsGlued_of_cases hL38 (d36GluedDiag_of_cases hL38 hL3 hO) hN

end CFSG.Quasithin
