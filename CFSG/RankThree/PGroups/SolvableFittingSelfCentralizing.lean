module

public import CFSG.RankThree.PGroups.SolvableTrivialComplementCore

public section

namespace CFSG.RankThree.PGroups

open Subgroup

theorem solvable_fitting_self_centralizing (U : Type*) [Group U] [Finite U]
    [Group.IsSolvable U] : centralizer (fittingSubgroup U : Set U) ≤ fittingSubgroup U := by
  rw [← generalizedFitting_eq_fittingSubgroup_of_isSolvable]
  exact centralizer_generalizedFitting_le U

end CFSG.RankThree.PGroups
