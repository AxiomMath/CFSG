module

public import CFSG.RankThree.GF2n.Stroth80.Sec94FreeMain
public import CFSG.RankThree.GF2n.Stroth80.Sec94FreeL56

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

theorem step94EndFree_holds (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) (h311bCard : Stroth311bCardStatement)
    (h312b : Stroth312bStatement) (hX : Classify.TheoremXStatement) : Step94EndFreeStatement :=
  step94EndFree_of_gen_notQB h34 h311a h311bComm h311bCard
    (step94Gen_holds h34 h311a h311bComm h311bCard h312b hX)
    (step94NotQB_holds h34 h311a h311bComm h311bCard h312b)

end CFSG.RankThree.GF2n.Stroth80
