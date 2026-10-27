module

public import CFSG.RankThree.GF2n.Smith81.Lin212Two
public import CFSG.RankThree.GF2n.Smith81.Lin3TwoLeaves

public section

namespace CFSG.RankThree.GF2n.Smith81

theorem lin3Statement_holds : Lin3Statement :=
  lin3Statement_of_two_leaves lin212TwoStatement_holds lin28TwoStatement_holds

end CFSG.RankThree.GF2n.Smith81
