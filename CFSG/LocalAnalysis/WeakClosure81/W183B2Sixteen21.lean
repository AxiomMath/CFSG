module

public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12c2Gt2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveEighteenSetting
public import CFSG.LocalAnalysis.WeakClosure81.SixFiveL
public import CFSG.SignalizerFunctorTheorem.Quadratic.Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

section Certified


theorem w183b2_sixteen21 (h162 : W3Thm162Gt2 G) {D : Data G} {V₀ V : Subgroup G}
    (hW : WeakClosureSetting D V₀ V) (hV₀ : V₀ ≠ ⊥) (hm : MBarGT D.M V₀ V 2) {n : ℕ}
    (hn : n < mBar D.M V₀ V hW.isElemAbelian) {x : G} (hO : InCalO n D.M V₀ V x) :
    Hyp64 n D.M V₀ V x := by
  have hH := hW.hyp6H
  have hV := hW.isElemAbelian
  have hM : D.M ≤ normalizer (V : Set G) := hH.normalizer_eq.symm.le
  have hM₀ := hH.le_normalizer₀
  have hm2 : 2 < mBar D.M V₀ V hV := (hW.pair.mBarGT_iff_lt_mBar 2).1 hm
  have hr : ((mSub V₀ + n : ℕ) : ℕ∞) < rMV D.M V := by
    have h1 := h162 D V₀ V hW hV₀ hm2
    refine lt_of_lt_of_le ?_ h1
    exact_mod_cast (by omega : mSub V₀ + n < mBar D.M V₀ V hV + mSub V₀)
  have hO1 : InCalO1 n D.M V₀ V x := (six_six hV hH.le hM hM₀ hn x).1 hO
  have hOS : InCalOStar n D.M V₀ V x := (hH.hyp65 hV₀ hO1).inCalOStar_of_lt_rMV hr
  exact hH.hyp64 hOS

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
