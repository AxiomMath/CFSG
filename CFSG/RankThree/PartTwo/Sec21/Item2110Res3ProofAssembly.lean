module

public import CFSG.RankThree.PartTwo.Sec21.Item2110Res3ProofHJ
public import CFSG.RankThree.PartTwo.Sec21.Item2110Res3ProofAL
public import CFSG.RankThree.PartTwo.Sec21.Item2110Res2ProofAssembly

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item2110Res3Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint

section Assembly

theorem item2110CentAJ_of_res3 (h211 : Item211) (h45 : Sec4.Item4_5) (h219 : Item219)
    (hD4 : KF2110ALInID4) : Item2110CentAJ :=
  item2110CentAJ_of h211 h45 h219 (item2110ALInI_of h211 h219 hD4)

theorem item2110Two_of_res3 (h211 : Item211) (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    (h426 : Sec4.Item4_26Theta) (h129 : Item129Bar) (h219 : Item219) (hD4 : KF2110ALInID4)
    (hF : Item2110JField) (hON : Item2110JON) : Item2110Two :=
  Item2110Res2Proof.item2110Two_of_parts h211 h45 h48 h426 h129 (item2110IData_of h219) hF hON
    (item2110CentAJ_of_res3 h211 h45 h219 hD4)

theorem item2110JThetaI_of_res3 (h211 : Item211) (h48 : Sec4.Item4_8)
    (h426 : Sec4.Item4_26Theta) (h219 : Item219) (hF : Item2110JField) (hON : Item2110JON) :
    Item2110JThetaI :=
  Item2110Res2Proof.item2110JThetaI_of h211 h48 h426 (item2110IData_of h219) hF hON

theorem item2110ThreeUnique_of_res3 (h211 : Item211) (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    (h426 : Sec4.Item4_26Theta) (h129 : Item129Bar) (h219 : Item219) (hD4 : KF2110ALInID4)
    (hF : Item2110JField) (hON : Item2110JON) (hKF : KF2110SylowNoncentral) :
    Item2110ThreeUnique :=
  Item2110Res2Proof.item2110ThreeUnique_of
    (item2110Two_of_res3 h211 h45 h48 h426 h129 h219 hD4 hF hON)
    (item2110TwoThree_of h45 (item2110JThetaI_of_res3 h211 h48 h426 h219 hF hON)
      (item2110CentAJ_of_res3 h211 h45 h219 hD4) hKF)

theorem item2110Three_of_res3 (h211 : Item211) (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    (h426 : Sec4.Item4_26Theta) (h129 : Item129Bar) (h219 : Item219) (hD4 : KF2110ALInID4)
    (hF : Item2110JField) (hON : Item2110JON) (hKF : KF2110SylowNoncentral) : Item2110Three :=
  Item2110Res2Proof.item2110Three_of (item2110JThetaI_of_res3 h211 h48 h426 h219 hF hON)
    (item2110ThreeUnique_of_res3 h211 h45 h48 h426 h129 h219 hD4 hF hON hKF)

theorem item2110One_of_res3 (h211 : Item211) (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    (h426 : Sec4.Item4_26Theta) (h129 : Item129Bar) (h219 : Item219) (hD4 : KF2110ALInID4)
    (hF : Item2110JField) (hON : Item2110JON) (hKF : KF2110SylowNoncentral) : Item2110One :=
  Sec21.item2110One_of (item2110Three_of_res3 h211 h45 h48 h426 h129 h219 hD4 hF hON hKF)
    (Item2110Res2Proof.item2110JTheta_of (item2110JThetaI_of_res3 h211 h48 h426 h219 hF hON)
      (item2110ThreeUnique_of_res3 h211 h45 h48 h426 h129 h219 hD4 hF hON hKF))

theorem item2112TwoGroupHJ_of_res3 (h211 : Item211) (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    (h426 : Sec4.Item4_26Theta) (h129 : Item129Bar) (h219 : Item219) (hD4 : KF2110ALInID4)
    (hF : Item2110JField) (hON : Item2110JON) (hKF : KF2110SylowNoncentral) :
    Item2112TwoGroupHJ :=
  item2112TwoGroupHJ_of (item2110Two_of_res3 h211 h45 h48 h426 h129 h219 hD4 hF hON) h45
    (item2110JThetaI_of_res3 h211 h48 h426 h219 hF hON)
    (item2110ThreeUnique_of_res3 h211 h45 h48 h426 h129 h219 hD4 hF hON hKF)
    (item2110CentAJ_of_res3 h211 h45 h219 hD4) h219

end Assembly

end CFSG.RankThree.PartTwo.Sec21.Item2110Res3Proof
