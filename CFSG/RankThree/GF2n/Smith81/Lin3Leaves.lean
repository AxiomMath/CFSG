module

public import CFSG.RankThree.GF2n.Smith81.Lin3Assembly
public import CFSG.RankThree.GF2n.Smith81.LinTLMixedConj
public import CFSG.RankThree.GF2n.Smith81.LinModule

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80


theorem lin31Statement_of_two (hTwo : Lin31TwoStatement) : Lin31Statement :=
  lin31Statement_of linBInStatement_holds lin31FwdStatement_holds hTwo

theorem lin3Statement_of_nine_leaves (hTwo : Lin31TwoStatement) (h28c : Lin28CondStatement)
    (hmod : LinModuleStatement) (h7 : Lin212C7Statement) (hrest : Lin212RestStatement)
    (h212two : Lin212TwoStatement) (h28two : Lin28TwoStatement) (h213 : Lin213Statement)
    (h26 : Lin26Statement) : Lin3Statement :=
  lin3Statement_of_leaves linBInStatement_holds lin31FwdStatement_holds hTwo h28c hmod h7 hrest
    h212two h28two h213 h26

theorem lin3Statement_of_eight_leaves (hTwo : Lin31TwoStatement) (h28c : Lin28CondStatement)
    (h7 : Lin212C7Statement) (hrest : Lin212RestStatement) (h212two : Lin212TwoStatement)
    (h28two : Lin28TwoStatement) (h213 : Lin213Statement) (h26 : Lin26Statement) :
    Lin3Statement :=
  lin3Statement_of_nine_leaves hTwo h28c linModuleStatement_holds h7 hrest h212two h28two h213 h26

end CFSG.RankThree.GF2n.Smith81
