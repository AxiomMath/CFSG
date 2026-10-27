module

public import CFSG.RankThree.GF2n.Smith81.Lin26Three
public import CFSG.RankThree.GF2n.Smith81.Lin26Two

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

theorem lin26ScalarStatement_holds : Lin26ScalarStatement := by
  intro G _ _ M Q Z B n V₁ V₂ hb hc hS hn
  rcases Nat.lt_or_ge n 3 with h | h
  · obtain rfl : n = 2 := by omega
    exact lin26Scalar_of_two G M Q Z B V₁ V₂ hb hc hS
  · exact lin26Scalar_of_three G M Q Z B n V₁ V₂ hb hc hS h

theorem lin26Statement_holds : Lin26Statement :=
  lin26Statement_of_scalar lin26ScalarStatement_holds

end CFSG.RankThree.GF2n.Smith81
