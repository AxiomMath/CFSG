module

public import CFSG.RankThree.PartTwo.Census.Sporadic.Klein
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.CoxeterM
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.CoxeterFi24
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.QuasithinUnique.SQTK TauCeti.Sporadic

theorem excluded433_M : Excluded433 (.sporadic .M) := by
  intro G _ _ hG eG
  refine hG.false_of_four_le_localRank (MulEquiv.refl G) Nat.prime_three (by norm_num) ?_
  refine four_le_localRank_three_of_coxeter monsterEdges Monster.coxeterMatrix (fun i j => ?_)
    (Coxeter.edgeGraph_connected 0 (by decide +kernel) (by decide +kernel))
    (Coxeter.edgeGraph_cliqueFree_three (by decide +kernel)) PresentedGroup.of
    (PresentedGroup.closure_range_of _)
    (fun i j => Coxeter.presentedGroup_coxeter_pow_eq_one _ _ i j) (K := ⊤) le_top
    (eG.trans (Monster.mulEquivPresentedGroupCoxeterAppend.trans Subgroup.topEquiv.symm))
    hG.nonabelian ![1, 3, 7, 10] ![0, 4, 8, 11] (by decide +kernel) (by decide +kernel) 5 2
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  rw [Monster.coxeterMatrix_apply, Monster.edges_def]
  rfl

theorem excluded433_Fi24Prime : Excluded433 (.sporadic .Fi24Prime) := by
  intro G _ _ hG eG
  refine hG.false_of_four_le_localRank (MulEquiv.refl G) Nat.prime_three (by norm_num) ?_
  refine four_le_localRank_three_of_coxeter fi24CoxeterEdges fi24AutomorphismCoxeterMatrix
    (fun i j => ?_) (Coxeter.edgeGraph_connected 11 (by decide +kernel) (by decide +kernel))
    (Coxeter.edgeGraph_cliqueFree_three (by decide +kernel)) PresentedGroup.of
    (PresentedGroup.closure_range_of _) fi24AutomorphismGroup_of_mul_of_pow
    (K := commutator Fi24AutomorphismGroup) le_rfl (eG.trans fi24PrimeGroupMulEquivCommutator)
    hG.nonabelian ![5, 11, 1, 7] ![6, 10, 2, 8] (by decide +kernel) (by decide +kernel) 9 4
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  rw [fi24AutomorphismCoxeterMatrix_apply, fi24AutomorphismEdges_def]
  rfl

end CFSG.RankThree.PartTwo.Census
