module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.Defs
public import CFSG.GH74.Orders.LieType

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)

theorem excl_L3_three {J : Type} [Group J] [Finite J] (e : LieModel J .PSL 3 3 1) : Excl J := by
  refine Or.inl ?_
  unfold Big27
  rw [CFSG.GH74.card_of_lieModel_PSL (by norm_num) e]
  decide

theorem excl_U3_three {J : Type} [Group J] [Finite J] (e : LieModel J .PSU 3 3 1) : Excl J := by
  refine Or.inl ?_
  unfold Big27
  rw [CFSG.GH74.card_of_lieModel_PSU (by norm_num) (by norm_num) e]
  decide

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg
