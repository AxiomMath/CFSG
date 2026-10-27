module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res12ProofQ1
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts3ProofAssembly

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open Item86ResProof

theorem item812_of_res20
    (h83 : Item83) (h83a : Item83After) (h45 : Sec4.Item4_5)
    (h48 : Sec4.Item4_8) (h418 : Item418Theta) (hUL : Pair84GammaUL) (hL : Item82TwoList)
    (hSp : Item8KFacts3.KF84Sp4ThreeCent) (hE9 : Item8KFacts3.KF84G2E9)
    (hD4 : Item8KFacts3.KF84D4OuterSU3) (hT : Pair86NonUnitary) (h87 : Item87) (h88 : Item88)
    (h84 : Pair84A) (h419 : Sec4.Item4_19ThetaJ3) (hJ3 : KF89NotJ3) (hcomp : KF89JCompNe)
    (h611 : Sec6.Item6_11_1) (hbYU : Fin812BMemYU) : Item812 :=
  item812_of_res18 h83 h83a h45 h48 h418 hUL hL hSp hE9 hD4 hT h87 h88 h84 h419 hJ3 hcomp h611
    hbYU (fin812Q1Cyclic_of h45 h84)

end CFSG.RankThree.PartTwo.Sec8
