module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveEighteenSetting
public import CFSG.LocalAnalysis.WeakClosure81.SixFiveL
public import CFSG.LocalAnalysis.WeakClosure81.W172OrbitDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12c2Gt2

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

section Certified


theorem w172_lem26 (h162 : W3Thm162Gt2 G) {D : Data G} {V₀ V : Subgroup G}
    (hW : WeakClosureSetting D V₀ V) (hV₀ : V₀ ≠ ⊥) (hm : MBarGT D.M V₀ V 2) :
    W172Lem26 D V₀ V := by
  intro x hO
  have hH := hW.hyp6H
  have hV := hW.isElemAbelian
  have hM : D.M ≤ normalizer (V : Set G) := hH.normalizer_eq.symm.le
  have hM₀ := hH.le_normalizer₀
  have hm2 : 2 < mBar D.M V₀ V hV := (hW.pair.mBarGT_iff_lt_mBar 2).1 hm
  have hm1 : 1 < mBar D.M V₀ V hV := by omega
  have hr : ((mSub V₀ + 1 : ℕ) : ℕ∞) < rMV D.M V := by
    have h1 := h162 D V₀ V hW hV₀ hm2
    refine lt_of_lt_of_le ?_ h1
    exact_mod_cast (by omega : mSub V₀ + 1 < mBar D.M V₀ V hV + mSub V₀)
  have hO1 : InCalO1 1 D.M V₀ V x := (six_six hV hH.le hM hM₀ hm1 x).1 hO
  have hOS : InCalOStar 1 D.M V₀ V x := (hH.hyp65 hV₀ hO1).inCalOStar_of_lt_rMV hr
  exact hH.hyp64 hOS

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
