module

public import CFSG.RankThree.PartTwo.Sec8.Item89Res2ProofMult
public import CFSG.RankThree.PartTwo.Sec8.Item89Res2ProofJTypeRee
public import CFSG.RankThree.PartTwo.Sec8.Item89Res2ProofUnitary
public import CFSG.RankThree.PartTwo.Sec8.Item812Res6ProofG2Two
public import CFSG.RankThree.PartTwo.Sec8.Item86ResProofKinds

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open Item86ResProof

theorem pair87Unitary_of_syl (h45 : Sec4.Item4_5) (hC : KF87UBComm) (hS : Pair87UnitarySyl) :
    Pair87Unitary :=
  pair87Unitary_of h45 kF87UnitaryJ_holds (pair87UnitaryY_of h45 hC hS)

theorem kF89JCompNe_of_lBalance (h45 : Sec4.Item4_5) (h84 : Pair84A)
    (hGW : Sec6.GWLBalanceStatement) : KF89JCompNe :=
  kF89JCompNe_of h45 h84 hGW (kF89JCentType_of kF89JCentTypeRee_holds) kF89JMult_holds

end CFSG.RankThree.PartTwo.Sec8
