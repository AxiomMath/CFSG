module

public import CFSG.RankThree.GF2n.Smith81.Lin28CondCaseII
public import CFSG.RankThree.GF2n.Smith81.Lin212Rest

public section

namespace CFSG.RankThree.GF2n.Smith81

theorem lin28CondStatement_holds : Lin28CondStatement := by
  intro G _ _ M Q Z B X x n V₁ V₂ hb hc hS hn hs hD
  rcases sit_theta_dichotomy hb hc hS hn hs with hI | hII
  · exact lin28Cond_caseI hb hc hS hn hs hI hD
  · exact lin28Cond_caseII hb hc hS hn hs hII

theorem lin3Statement_of_five_leaves (hcompl : Lin212ComplStatement)
    (h212two : Lin212TwoStatement) (h28two : Lin28TwoStatement) (h213 : Lin213Statement)
    (h26 : Lin26Statement) : Lin3Statement :=
  lin3Statement_of_seven_leaves_compl lin28CondStatement_holds
      (lin212C7_of lin28CondStatement_holds) hcompl h212two h28two h213 h26

end CFSG.RankThree.GF2n.Smith81
