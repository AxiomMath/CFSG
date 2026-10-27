module

public import CFSG.RankThree.GF2n.Tim78Thm1
public import CFSG.Milestones.CL_LIT_Goldschmidt_strongly_closed_abelian

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open

theorem goldschmidtInput : GoldschmidtInput :=
  fun X _ _ S A hAS hAab hclosed =>
    CFSG.Milestones.cl_lit_goldschmidt_strongly_closed_abelian X S A hAS hAab hclosed

theorem tim78_theorem1_of_eight_le' {G : Type} [Group G] [Finite G]
    (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput) {M B : Subgroup G}
    (H : HypH M B) (h8 : 8 ≤ Nat.card ↥(PartTwo.omegaOneSub B)) :
    Assembly.IsElemAbelian 2 B :=
  tim78_theorem1_of_eight_le goldschmidtInput hCen hU H h8

end CFSG.RankThree.GF2n.Tim78
