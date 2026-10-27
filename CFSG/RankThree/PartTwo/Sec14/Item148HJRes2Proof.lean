module

public import CFSG.RankThree.PartTwo.Sec14.Item148HJRes2ProofYd
public import CFSG.RankThree.PartTwo.Sec14.Item148HJResProof
public import CFSG.RankThree.PartTwo.Sec14.Item148HJRes2ProofInner

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13

section Certificates

theorem step148HJ_of_res2 (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h134 : Item134)
    (h427 : Sec4.Item4_27) (hGW : Sec6.GWLBalanceStatement) (h41 : Sec4.Item4_1LargePrime)
    (hY6 : Step148HJTypeYdONA6) (hY5 : Step148HJTypeYdONA5) (hKF : KF148HJA6Outer)
    (hM : Step148HJM24Outer2) (hNA6 : Step148HJNormalInnerA6) (hNON : Step148HJNormalInnerON)
    (hH : Step148HJHJOuter2) (h5 : Step148HJA5Inner2) : Step148HJ :=
  step148HJ_of_res_narrow h45 h48 h134 h427 hGW h41 (step148HJTypeYdOuter_of_on hY6 hY5) hKF
    (step148HJM24Outer_of_outer2 hM) (step148HJNormalInner_of_res2 hNA6 hNON)
    step148HJNormalOuterON_holds (step148HJHJOuter_of_outer2 hH) (step148HJA5Inner_of_inner2 h5)

end Certificates

end CFSG.RankThree.PartTwo.Sec14
