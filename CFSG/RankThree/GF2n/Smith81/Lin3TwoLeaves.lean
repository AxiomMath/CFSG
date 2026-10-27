module

public import CFSG.RankThree.GF2n.Smith81.Lin213Outside
public import CFSG.RankThree.GF2n.Smith81.Lin3ThreeLeaves

public section

namespace CFSG.RankThree.GF2n.Smith81

theorem lin213Statement_of_two (htwo : Lin212TwoStatement) :
    Lin213Statement :=
  lin213Statement_of (lin212Statement_of_two htwo)

theorem lin3Statement_of_two_leaves (h212two : Lin212TwoStatement)
    (h28two : Lin28TwoStatement) : Lin3Statement :=
  lin3Statement_of_three_leaves h212two h28two (lin213Statement_of_two h212two)

end CFSG.RankThree.GF2n.Smith81
