module

public import CFSG.RankThree.PartTwo.Sec21.FF79Sec4Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCenter

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

theorem ff79_JL5_holds :
    FF79_JL5 := by
  intro G _ _ b J h
  have hle : J ≤ Subgroup.centralizer ({b} : Set G) := h.std.1
  have hq : CFSG.IsQuasisimple ↥J :=
    CFSG.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle).symm h.std.2.1.1
  have hm : StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) .PSL 5 2 1 := h.model
  have hL : CFSG.Blueprint.LieModel (↥J ⧸ Subgroup.center ↥J) .PSL 5 2 1 :=
    .inl ⟨by decide, hm⟩
  have hZ : Subgroup.center ↥J = ⊥ :=
    CFSG.OddStandard.SmallF3.HypA2Leaves.a2l_center_eq_bot_psl52 hq hL
  exact CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot) hm

end CFSG.RankThree.PartTwo.Sec21.FF79
