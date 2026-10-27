module

public import CFSG.RankThree.Co2.CentC
public import CFSG.Milestones.CL_LIT_Goldschmidt_strongly_closed_abelian

public noncomputable section

namespace CFSG.RankThree.Co2

theorem goldschmidtStatement : GoldschmidtStatement :=
  fun X _ _ S A hAS hAab hclosed =>
    CFSG.Milestones.cl_lit_goldschmidt_strongly_closed_abelian X S A hAS hAab hclosed

theorem Co2CentHyp.card_IG {G : Type} [Group G] (h : Co2CentHyp G) :
    Nat.card h.IG = 41287680 :=
  h.card_IG_of_goldschmidt goldschmidtStatement

end CFSG.RankThree.Co2
