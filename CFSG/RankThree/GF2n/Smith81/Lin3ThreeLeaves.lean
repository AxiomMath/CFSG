module

public import CFSG.RankThree.GF2n.Smith81.Lin212Compl
public import CFSG.RankThree.GF2n.Smith81.Lin26

public section

namespace CFSG.RankThree.GF2n.Smith81

theorem lin3Statement_of_three_leaves (h212two : Lin212TwoStatement)
    (h28two : Lin28TwoStatement) (h213 : Lin213Statement) : Lin3Statement :=
  lin3Statement_of_five_leaves lin212Compl_holds h212two h28two h213 lin26Statement_holds

theorem lin212Statement_of_two (htwo : Lin212TwoStatement) :
    Lin212Statement :=
  have h31 := lin31Statement_holds
  have hcond := lin212Cond_of lin28CondStatement_holds linModuleStatement_holds
    (lin212C7_of lin28CondStatement_holds) h31
  lin212Statement_of hcond (lin28aBelow_of_parity (lin28aEven_of h31 hcond)
    (lin28aOdd_of h31 hcond)) (lin212Rest_of (lin212RestFirst_of lin28CondStatement_holds)
    lin212Compl_holds) htwo

end CFSG.RankThree.GF2n.Smith81
