module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Defs
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinU4Two14Inner
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinU4Two14Outer
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135Ctx
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallU4Nat
import CFSG.GroupTheory.E3Params

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open CFSG.HardMathSupport.U4FF (disp)

theorem finU4Two14_holds :
    FinU4Two14 := by
  intro W _ _ hW Y L g hctx hgY hg2 hL hcard
  have hZ := finU4_center_eq_bot hctx hL
  have hL' : LieModel ↥L .PSU 4 2 1 := CFSG.Blueprint.LieModel.of_quotient_center hZ hL
  have hU4 : CFSG.LocalAnalysis.RankThreeUC.IsU4Group 1 L := finU4_isU4Group hL'
  have hI := hctx.2.2.2.2.2
  have hirr : CFSG.LocalAnalysis.RankThreeUC.IsIrrOn L := fun J hJ => hI.2.2.2 J hJ bot_le le_top
  haveI : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  haveI : Fact (∀ s : W, s * s = 1) := ⟨fun s => by rw [← pow_two]; exact hW s⟩
  have hgg : g * g = 1 := by
    have h1 := pow_orderOf_eq_one g
    rwa [hg2, pow_two] at h1
  have hg1 : g ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hg2
    exact absurd hg2 (by norm_num)
  have hLY : L ≤ Y := hctx.2.2.1
  have hYN : Y ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLY).mp (w135_normal_of_ctx hctx)
  rw [CFSG.GroupTheory.mQuot_top_eq_rkIdx, Thm14_5.rkIdx_fixV_zpowers_eq_disp g]
  by_cases hgL : g ∈ L
  · have h6 := finU4_inner_disp_ge hU4 hirr hcard hgL hg1 hgg
    omega
  · exact finU4_outer_disp_ge hU4 hirr hcard (hYN hgY) hgg hgL

end CFSG.LocalAnalysis.WeakClosure81
