module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslOuterFinish

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Finset
open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)

theorem w135c2_psl_outer_semilinear
    {W : Type} [CommGroup W] [Finite W]
    {Y L : Subgroup (MulAut W)} {t : MulAut W} (hRows : Chev135Rows)
    (hW : ∀ w : W, w ^ 2 = 1) (hctx : Is135Context Y L) (htY : t ∈ Y) (ht2 : orderOf t = 2)
    (hm : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3) {n f : ℕ} (hn41 : ¬ (n = 4 ∧ f = 1))
    (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .PSL n 2 f)
    (hsemi : rk W = 2 * E3.mQuot ⊤ (fixV (Subgroup.zpowers t))) : W4Lem13_5Concl W Y L t := by
  have hq : IsQuasisimple ↥L := hctx.2.2.2.2.1
  have hirr : IsIrrOn L ⊤ ⊥ := hctx.2.2.2.2.2
  have hnab : ∃ a ∈ L, ∃ b ∈ L, a * b ≠ b * a := by
    obtain ⟨x, y, hxy⟩ := hq.2.2
    obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
    refine ⟨x', x'.2, y', y'.2, fun h => hxy ?_⟩
    have hL : (x' * y' : ↥L) = y' * x' := Subtype.ext h
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hL]
  have htN : ∀ g ∈ L, t * g * t⁻¹ ∈ L := by
    intro g hg
    have hLY : L ≤ Y := hctx.2.2.1
    have hmem := (w135_normal_of_ctx hctx).conj_mem
      (⟨g, hLY hg⟩ : ↥Y) (Subgroup.mem_subgroupOf.mpr hg) (⟨t, htY⟩ : ↥Y)
    simpa using (Subgroup.mem_subgroupOf.mp hmem)
  have hA3 : 3 ≤ gs03Bound .PSL n f := w135c2_three_le_gs03Bound hlie
  have hgen : rk W ≤ gs03Bound .PSL n f * E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) := by
    rw [hsemi]
    exact Nat.mul_le_mul_right _ (by omega)
  obtain ⟨k, d, hk, hrk, hrange⟩ := w135c2_range hW hirr hnab htN ht2 hm hA3 hgen
  exact w135c2_psl_outer_finish hRows hW hctx htY ht2 hm hn41 hlie hk hrk hrange

end CFSG.LocalAnalysis.WeakClosure81
