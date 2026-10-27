module

import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpTwo
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpFour
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpInner
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpInnerSmall
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpOuterEven
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2NatB
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)

theorem w135c2_sp
    {W : Type} [CommGroup W] [Finite W] {Y L : Subgroup (MulAut W)}
    {t : MulAut W} (hW : ∀ w : W, w ^ 2 = 1) (hctx : Is135Context Y L) (htY : t ∈ Y)
    (ht2 : orderOf t = 2) (hm : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3) {n f : ℕ}
    (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .PSp n 2 f) : W4Lem13_5Concl W Y L t := by
  obtain ⟨-, hf1, hn2, -⟩ := LieModel.admissible hlie
  by_cases hf1' : f = 1
  · subst hf1'
    exact w135c2_sp_two hW hctx htY ht2 hm hlie
  · by_cases hn2' : n = 2
    · subst hn2'
      exact w135c2_sp_four hW hctx htY ht2 hm hlie
    · have hf2 : 2 ≤ f := by omega
      have hn3 : 3 ≤ n := by omega
      by_cases htL : t ∈ L
      · have hle := w135c2_sp_inner_le_mQuot hW hctx htL ht2 hlie
        have hf23 : f = 2 ∨ f = 3 := by omega
        obtain ⟨hS, hNat⟩ :=
          w135c2_sp_inner_small_natural hW hctx htL ht2 hm hn3 hf23 hlie
        exact w135c2_natural hctx htY ht2 hW
          (Or.inl ⟨2 * n, f, Or.inr (Or.inl ⟨hS, hNat⟩)⟩)
      · have h4 := w135c2_sp_outer_four_le hW hctx htY htL ht2 hn3 hf2 hlie
        exact absurd h4 (by omega)

end CFSG.LocalAnalysis.WeakClosure81
