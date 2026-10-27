module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslModules
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2NatB
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2MainA

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)

theorem w135c2_psl_outer_finish
    {W : Type} [CommGroup W] [Finite W]
    {Y L : Subgroup (MulAut W)} {t : MulAut W} (hRows : Chev135Rows)
    (hW : ∀ w : W, w ^ 2 = 1) (hctx : Is135Context Y L) (htY : t ∈ Y) (ht2 : orderOf t = 2)
    (hm : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3) {n f : ℕ} (hn41 : ¬ (n = 4 ∧ f = 1))
    (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .PSL n 2 f) {k d : ℕ}
    (hk : Nat.card (LEnd L) = 2 ^ k) (hrk : rk W = k * d)
    (hrange : (k = 1 ∧ d ≤ 3 * gs03Bound .PSL n f) ∨
      ((k = 2 ∨ k = 3) ∧ d ≤ gs03Bound .PSL n f)) : W4Lem13_5Concl W Y L t := by
  have hq : IsQuasisimple ↥L := hctx.2.2.2.2.1
  have hirr : IsIrrOn L ⊤ ⊥ := hctx.2.2.2.2.2
  rcases chev2SmallModules_psl hW hq hirr hn41 hlie hk hrk hrange with hnat | hitem | hrow
  · exact w135c2_natural hctx htY ht2 hW hnat
  · exact w135c2_concl_of_item3 hitem
  · exfalso
    have hcard : Nat.card W = 2 ^ (k * d) := by rw [w135_card_eq_two_pow_rk hW, hrk]
    have h4 := w135c2_rows_of_idx hRows hrow W hW Y L t hctx htY ht2 hlie hcard
    omega

end CFSG.LocalAnalysis.WeakClosure81
