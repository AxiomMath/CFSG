module

public import CFSG.RankThree.PartOne.S8.Statements
import CFSG.RankThree.PartOne.S8.PrepFitting
import CFSG.RankThree.PartOne.S8.PrepComponents
import CFSG.RankThree.OddKernel.ThreeComplementQuotient
import CFSG.RankThree.GroupTheory.SteinbergBKLocalCoreNormalizesComponent

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly.LowTwoRank CFSG.RankThree.LocalRank CFSG.RankThree.PartOne.S8
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.RankThree.GroupTheory.SteinbergBK
  (local_solvable_core_normalizes_prime_divisible_component)
open CFSG.SectionRank (IsKGroupCat)

theorem original_theta_free_quotient_component_action_preparation :
    OriginalThetaFreeQuotientComponentActionPreparation := by
  intro X _ _ hK hX p hp hp3 N _ hN hθ E hE hEc t ht ht1
  have hp2 : p ≠ 2 := by omega
  have hrankX : localRank p X ≤ 3 :=
    (CFSG.RankThree.OddKernel.localRank_le_evenRank hp hp2).trans hX
  have hrankQ : localRank p (X ⧸ N) ≤ 3 :=
    (CFSG.RankThree.Classical2.localRank_quotient_le hp hp2 N hN).trans hrankX
  have hFit := fittingSubgroup_eq_pCore_of_theta_eq_bot hp hθ
  have hZE := isPGroup_center_layer_of_theta_eq_bot hp hθ
  have hset := (CFSG.RankThree.GroupTheory.SteinbergBY.section_nine_residual_to_intersection hp
    hp2 E).1 t ht ht1
  obtain ⟨hsolv, hDp, hDS, hDF, hcop⟩ := localCoreProduct_facts hp hE ht ht1 hθ
  have hKQ : IsKGroupCat (X ⧸ N) := hK.quotient N
  have hEall : ∀ L : Subgroup (X ⧸ N), IsComponent L →
      E ≤ Subgroup.normalizer (L : Set (X ⧸ N)) := fun L hL =>
    plane_normalizes_quotient_component hX hp hp3 N hN (IsElementaryAbelian.isPGroup p E) hL
  refine ⟨hrankX, hrankQ, hFit, hZE, hset, hsolv, hDp, hDS, hDF, hcop, fun L hL => ?_⟩
  have hEL := hEall L hL
  refine ⟨hKQ L (Subgroup.center L) hL.1.2.1, hEL, commutator_normalizes_component hEall hL,
    fun hpL => ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  have hord : ∃ k : ℕ, orderOf t = p ^ k := by
    refine ⟨1, ?_⟩
    rw [pow_one]
    exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (p := p) t ht) ht1
  exact local_solvable_core_normalizes_prime_divisible_component hp hL hpL hZE hord (hEL ht)

end CFSG.RankThree.PartOne
