module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res7ProofD4N
public import CFSG.RankThree.PartTwo.Sec8.Item86Res2ProofAssembly

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open Item86ResProof

theorem pair86GTwoN_of_res7 (h45 : Sec4.Item4_5) (h418 : Item418Theta) (hO : KF84OuterL2)
    (hR : KF84FieldReeStd) (hS : KF86D4ShiftConj) : Pair86GTwoN :=
  pair86GTwoN_of h418 (kF84FieldStd_of hO hR) (pair86D4N_of h45 h418 hO hR hS)

theorem choice86Var_of_res7 (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h418 : Item418Theta)
    (hO : KF84OuterL2) (hR : KF84FieldReeStd) (hGT : KF83GTwoTwo) (hU : Pair84GammaU)
    (hN : Pair84GammaNonempty) (h1 : Pair86One) (hS : KF86D4ShiftConj) :
    Item83Proof.Choice86Var :=
  choice86Var_of_s315 h45 h48 h418 hO hR hGT hU hN h1 (pair86D4_of h45 h418 hO hR hS)
    (pair86D4N_of h45 h418 hO hR hS)

end CFSG.RankThree.PartTwo.Sec8
