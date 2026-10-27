module

public import CFSG.RankThree.PartTwo.Sec8.Item86Res2Proof84
public import CFSG.RankThree.PartTwo.Sec8.Item86Res2Proof85
public import CFSG.RankThree.PartTwo.Sec8.Item86Res2Proof86
public import CFSG.RankThree.PartTwo.Sec8.Item86Res2ProofIndep

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item86ResProof

open CFSG.RankThree.PartTwo.Sec8.Item83Proof

theorem choice86Var_of_s315 (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h418 : Item418Theta)
    (hO : KF84OuterL2) (hR : KF84FieldReeStd) (hGT : KF83GTwoTwo) (hU : Pair84GammaU)
    (hN : Pair84GammaNonempty) (h1 : Pair86One) (hD4 : Pair86D4) (hD4N : Pair86D4N) :
    Choice86Var :=
  have hKB : KF83KBarTwo := kF83KBarTwo_of_even (kF83KBarEven_of hO hR)
  have hGI : KF83IndepGTwo := kF83IndepGTwo_of_two hGT
  have hInd : KF83Indep := kF83Indep_of hGI
  have hF : KF84FieldStd := kF84FieldStd_of hO hR
  choice86Var_of_narrowU_item45 h45 (pair84PartnerU_of h418 hKB hInd hF hU hN)
    (pair85Exists_of h45 h48 hKB hInd hO hR) (pair86Exists_of h418 hF h1 hD4) hKB hGI
    (pair86GTwoN_of h418 hF hD4N)

end CFSG.RankThree.PartTwo.Sec8.Item86ResProof
