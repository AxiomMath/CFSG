module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeSmallDefs
import CFSG.LocalAnalysis.StandardType.GGTableBExcSmall
import CFSG.RankThree.PartTwo.Sec21.Item223RankResProofAut

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly

section G2Rank

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover

theorem svRankG2_holds :
    SVRank (fun t => t = .G2) := by
  intro lab hlab ht
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hlab
  subst ht
  have hn2 : 2 ≤ n := hlab.2.2
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq'⟩ := hQ
  refine ⟨K, i1, i2, hK, hq', fun _ _ B hB hBI => ?_⟩
  haveI : CharP K 2 := charP_two_of_card hK
  haveI := TableBExc.finite_recipeGroup .G2 K
  have hI := chevIDImage_subset_inn_of_top (τ := .G2) (K := K)
    (TableB.torusSubgroup_eq_top_of_mul_eq_smul _ K TableB.cartanG2_inv fun s => ⟨s, pow_one s⟩)
  have hBinn := fun φ (hφ : φ ∈ B) => ((Subgroup.closure_le _).mpr hI) (hBI hφ)
  obtain ⟨A, hA, hAc⟩ :=
    TableBSymp.exists_of_subset_inn (TableBExc.center_recipeGroup_eq_bot .G2 K) hBinn hB
  have hmap := TableB.isElemAbelian_map hA (TableBExc.recipeEquiv .G2 K).toMonoidHom
  have h1 := CFSG.RankThree.PartTwo.Sec21.Item223RankResProof.adjointG2_even_card_le_nine
    hK hn2 (A.map (TableBExc.recipeEquiv .G2 K).toMonoidHom) hmap
  rw [Subgroup.card_map_of_injective (TableBExc.recipeEquiv .G2 K).injective, hAc] at h1
  exact h1

end G2Rank

end CFSG.StandardType.TablePThreeKG

end
