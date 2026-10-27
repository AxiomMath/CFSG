module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2ExcTag
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2ExcSz
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2ExcRee
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2ExcTits
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2ExcG2

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

theorem w135c2_four_le_mQuot_direct
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y L : Subgroup (MulAut W)} {t : MulAut W} (hctx : Is135Context Y L) (htY : t ∈ Y)
    (ht2 : orderOf t = 2) {tag : StatedLieTag} {n f : ℕ} (hdir : Chev2DirectTag tag)
    (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) tag n 2 f) :
    4 ≤ E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) := by
  rcases hdir with rfl | rfl | rfl | rfl
  · exact w135c2_four_le_mQuot_sz hW hctx htY ht2 hlie
  · exact w135c2_four_le_mQuot_ree hW hctx htY ht2 hlie
  · exact w135c2_four_le_mQuot_tits hW hctx htY ht2 hlie
  · exact w135c2_four_le_mQuot_g2 hW hctx htY ht2 hlie

theorem w135c2_branch_direct
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y L : Subgroup (MulAut W)} {t : MulAut W} (hctx : Is135Context Y L) (htY : t ∈ Y)
    (ht2 : orderOf t = 2) (hm : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3)
    {tag : StatedLieTag} {n f : ℕ} (hdir : Chev2DirectTag tag)
    (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) tag n 2 f) : W4Lem13_5Concl W Y L t := by
  have h4 := w135c2_four_le_mQuot_direct hW hctx htY ht2 hdir hlie
  omega

end CFSG.LocalAnalysis.WeakClosure81
