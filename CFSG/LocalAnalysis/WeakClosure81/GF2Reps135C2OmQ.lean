module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQPlus
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinus
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2NatB
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PsuOuterInvolution
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)

theorem w135c2_omPlus_f2
    {W : Type} [CommGroup W] [Finite W] {Y L : Subgroup (MulAut W)}
    {t : MulAut W} (hW : ∀ w : W, w ^ 2 = 1) (hctx : Is135Context Y L) (htY : t ∈ Y)
    (ht2 : orderOf t = 2) (hm : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3) {n f : ℕ}
    (hn : 5 ≤ n) (hf : 2 ≤ f)
    (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .POmegaPlus n 2 f) :
    W4Lem13_5Concl W Y L t := by
  obtain ⟨y, hyL, hy1, hyy, hym⟩ := w135c2_psu_outer_involution hW hctx htY ht2
  have hy2 : orderOf y = 2 := orderOf_eq_prime (by rwa [pow_two]) hy1
  obtain ⟨hIs, hNat⟩ := w135c2_omPlus_natural_of_le_six hW hctx hyL hy2 (by omega) hn hf hlie
  exact w135c2_natural hctx htY ht2 hW
    (Or.inl ⟨2 * n, f, Or.inr (Or.inr (Or.inl ⟨hIs, hNat⟩))⟩)

theorem w135c2_omMinus_f2
    {W : Type} [CommGroup W] [Finite W] {Y L : Subgroup (MulAut W)}
    {t : MulAut W} (hW : ∀ w : W, w ^ 2 = 1) (hctx : Is135Context Y L) (htY : t ∈ Y)
    (ht2 : orderOf t = 2) (hm : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3) {n f : ℕ}
    (hn : 4 ≤ n) (hf : 2 ≤ f)
    (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .POmegaMinus n 2 f) :
    W4Lem13_5Concl W Y L t := by
  obtain ⟨y, hyL, hy1, hyy, hym⟩ := w135c2_psu_outer_involution hW hctx htY ht2
  have hy2 : orderOf y = 2 := orderOf_eq_prime (by rwa [pow_two]) hy1
  obtain ⟨hIs, hNat⟩ := w135c2_omMinus_natural_of_le_six hW hctx hyL hy2 (by omega) hn hf hlie
  exact w135c2_natural hctx htY ht2 hW
    (Or.inl ⟨2 * n, f, Or.inr (Or.inr (Or.inr ⟨hIs, hNat⟩))⟩)

end CFSG.LocalAnalysis.WeakClosure81
