module

public import CFSG.RankThree.PartOne.Census3.OpenCases
import CFSG.RankThree.PartTwo.Census.Sporadic.Fi22
import CFSG.RankThree.PartTwo.Census.Sporadic.Klein
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.CoxeterM
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.CoxeterFi24
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Seed.Fi22

public section

namespace CFSG.RankThree.PartOne.Census3

open CFSG.Blueprint CFSG.QuasithinUnique.SQTK CFSG.RankThree.PartTwo.Census TauCeti
  TauCeti.Sporadic

theorem excludedIndex_Fi22 : ExcludedIndex (.sporadic .Fi22) :=
  excludedIndex_of_equiv (T := NativeSporadic.Fi22) (fun _ => nonempty_mulEquiv_carrier_Fi22)
    Nat.prime_three (by norm_num) four_le_localRank_three_Fi22

theorem excludedIndex_M : ExcludedIndex (.sporadic .M) := by
  intro G _ _ _ hnonab eG
  refine four_le_twoLocalOddRank_of_localRank Nat.prime_three (by norm_num) ?_
  refine four_le_localRank_three_of_coxeter monsterEdges Monster.coxeterMatrix (fun i j => ?_)
    (Coxeter.edgeGraph_connected 0 (by decide +kernel) (by decide +kernel))
    (Coxeter.edgeGraph_cliqueFree_three (by decide +kernel)) PresentedGroup.of
    (PresentedGroup.closure_range_of _)
    (fun i j => Coxeter.presentedGroup_coxeter_pow_eq_one _ _ i j) (K := ⊤) le_top
    (eG.trans (Monster.mulEquivPresentedGroupCoxeterAppend.trans Subgroup.topEquiv.symm))
    hnonab ![1, 3, 7, 10] ![0, 4, 8, 11] (by decide +kernel) (by decide +kernel) 5 2
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  rw [Monster.coxeterMatrix_apply, Monster.edges_def]
  rfl

theorem excludedIndex_Fi24Prime : ExcludedIndex (.sporadic .Fi24Prime) := by
  intro G _ _ _ hnonab eG
  refine four_le_twoLocalOddRank_of_localRank Nat.prime_three (by norm_num) ?_
  refine four_le_localRank_three_of_coxeter fi24CoxeterEdges fi24AutomorphismCoxeterMatrix
    (fun i j => ?_) (Coxeter.edgeGraph_connected 11 (by decide +kernel) (by decide +kernel))
    (Coxeter.edgeGraph_cliqueFree_three (by decide +kernel)) PresentedGroup.of
    (PresentedGroup.closure_range_of _) fi24AutomorphismGroup_of_mul_of_pow
    (K := commutator Fi24AutomorphismGroup) le_rfl (eG.trans fi24PrimeGroupMulEquivCommutator)
    hnonab ![5, 11, 1, 7] ![6, 10, 2, 8] (by decide +kernel) (by decide +kernel) 9 4
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  rw [fi24AutomorphismCoxeterMatrix_apply, fi24AutomorphismEdges_def]
  rfl

theorem theoremThreeCase_sporadic_of (hCo1 : ExcludedIndex (.sporadic .Co1))
    (hFi23 : ExcludedIndex (.sporadic .Fi23)) (hB : RankFourBabyMonster) (s : SporadicName) :
    TheoremThreeCase (.sporadic s) := by
  by_cases hs : s ∈ sporadicsThm3
  · exact fun G _ _ _ e => TheoremThreeList.of_sporadic hs e
  · cases s
    case Co1 => exact hCo1.case
    case Fi22 => exact excludedIndex_Fi22.case
    case Fi23 => exact hFi23.case
    case Fi24Prime => exact excludedIndex_Fi24Prime.case
    case B => exact hB.case
    case M => exact excludedIndex_M.case
    all_goals exact (hs (by simp [sporadicsThm3])).elim

end CFSG.RankThree.PartOne.Census3
