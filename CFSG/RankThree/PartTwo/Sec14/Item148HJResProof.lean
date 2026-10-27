module

public import CFSG.RankThree.PartTwo.Sec14.Item148HJResProofYd
public import CFSG.RankThree.PartTwo.Sec14.Item148HJResProofTypes

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13

section Certificates

theorem step148HJ_of_res_a6 (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h134 : Item134)
    (h427 : Sec4.Item4_27) (hGW : Sec6.GWLBalanceStatement) (h41 : Sec4.Item4_1LargePrime)
    (hYdO : Step148HJTypeYdOuter) (hA6 : Step148HJTypeJOuterA6) (hM : Step148HJM24)
    (hN : Step148HJNormal) (hH : Step148HJHJ) (h5 : Step148HJA5) : Step148HJ :=
  step148HJ_of_yd h45 h48 (step148HJTypeYd_of_outer hYdO)
    (step148HJTypeJ_of_outer (step148HJTypeJOuter_of_a6 h427 hGW h41 h134 h48 hA6)) hM hN hH h5

theorem step148HJ_of_res (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h134 : Item134)
    (h427 : Sec4.Item4_27) (hGW : Sec6.GWLBalanceStatement) (h41 : Sec4.Item4_1LargePrime)
    (hYdO : Step148HJTypeYdOuter) (hKF : KF148HJA6Outer) (hM : Step148HJM24)
    (hN : Step148HJNormal) (hH : Step148HJHJ) (h5 : Step148HJA5) : Step148HJ :=
  step148HJ_of_res_a6 h45 h48 h134 h427 hGW h41 hYdO (step148HJTypeJOuterA6_of_kf hKF h41) hM hN
    hH h5

theorem step148HJ_of_res_narrow (h45 : Sec4.Item4_5)
    (h48 : Sec4.Item4_8) (h134 : Item134) (h427 : Sec4.Item4_27)
    (hGW : Sec6.GWLBalanceStatement) (h41 : Sec4.Item4_1LargePrime)
    (hYdO : Step148HJTypeYdOuter) (hKF : KF148HJA6Outer) (hM : Step148HJM24Outer)
    (hNI : Step148HJNormalInner) (hNO : Step148HJNormalOuterON) (hH : Step148HJHJOuter)
    (h5 : Step148HJA5Inner) : Step148HJ :=
  have hTYd := step148HJTypeYd_of_outer hYdO
  step148HJ_of_res h45 h48 h134 h427 hGW h41 hYdO hKF
    (step148HJM24_of_outer h45 h48 h134 h427 hGW h41 hTYd hM)
    (step148HJNormal_of_res h45 h48 h134 h427 hGW h41 hTYd hNI hNO)
    (step148HJHJ_of_outer h45 h48 h134 h427 hGW h41 hTYd hH)
    (step148HJA5_of_inner h45 h48 h134 h427 hGW h41 hTYd h5)

end Certificates

end CFSG.RankThree.PartTwo.Sec14
