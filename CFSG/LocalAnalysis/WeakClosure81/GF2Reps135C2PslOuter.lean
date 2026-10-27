module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslOuterLinear
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslOuterSemilinear

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)

theorem w135c2_psl_outer
    {W : Type} [CommGroup W]
    [Finite W] {Y L : Subgroup (MulAut W)} {t : MulAut W} (hRows : Chev135Rows)
    (hW : ∀ w : W, w ^ 2 = 1) (hctx : Is135Context Y L) (htY : t ∈ Y) (htL : t ∉ L)
    (ht2 : orderOf t = 2) (hm : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3) {n f : ℕ}
    (hn41 : ¬ (n = 4 ∧ f = 1)) (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .PSL n 2 f) :
    W4Lem13_5Concl W Y L t := by
  classical
  have hirr : IsIrrOn L ⊤ ⊥ := hctx.2.2.2.2.2
  have htN : ∀ g ∈ L, t * g * t⁻¹ ∈ L := by
    intro g hg
    have hLY : L ≤ Y := hctx.2.2.1
    have hmem := (w135_normal_of_ctx hctx).conj_mem
      (⟨g, hLY hg⟩ : ↥Y) (Subgroup.mem_subgroupOf.mpr hg) (⟨t, htY⟩ : ↥Y)
    simpa using (Subgroup.mem_subgroupOf.mp hmem)
  obtain ⟨k, d, -, hk, hrk, hcase⟩ := w135c2_dichotomy hW hirr htN ht2
  rcases hcase with ⟨r, hr1, hr⟩ | ⟨-, hsemi⟩
  · exact w135c2_psl_outer_linear hRows hW hctx htY htL ht2 hm hn41 hlie hk hrk hr hr1
  · exact w135c2_psl_outer_semilinear hRows hW hctx htY ht2 hm hn41 hlie hsemi

end CFSG.LocalAnalysis.WeakClosure81
