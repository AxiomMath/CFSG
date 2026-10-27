module

public import CFSG.RankThree.PartTwo.Sec21.Item2110Res2ProofTheta
public import CFSG.RankThree.PartTwo.Sec21.Item2110Res2ProofFinal
public import CFSG.RankThree.PartTwo.Sec21.Item21Res6ProofTen

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item2110Res2Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint

theorem item2110JTheta_of (hJ : Item2110JThetaI) (hU : Item2110ThreeUnique) : Item2110JTheta :=
  jTheta_of hJ hU

section Assembly

theorem item2110One_of_parts (h211 : Item211) (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    (h426 : Sec4.Item4_26Theta) (h129 : Item129Bar) (hI : Item2110IData) (hF : Item2110JField)
    (hON : Item2110JON) (hC : Item2110CentAJ) (h23 : Item2110TwoThree) : Item2110One :=
  Sec21.item2110One_of
    (item2110Three_of_parts h211 h45 h48 h426 h129 hI hF hON hC h23)
    (jTheta_of_parts h211 h45 h48 h426 h129 hI hF hON hC h23)

theorem item2115_of_parts (h211 : Item211) (h213 : Item213) (h214 : Item214) (h215 : Item215)
    (h217 : Item217) (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) (hL3 : Item2115LThree)
    (hU4S : Item2115U4Signalizer) (h48 : Sec4.Item4_8) (h426 : Sec4.Item4_26Theta)
    (h129 : Item129Bar) (hI : Item2110IData) (hF : Item2110JField) (hON : Item2110JON)
    (hC : Item2110CentAJ) (h23 : Item2110TwoThree) (hTGHJ : Item2112TwoGroupHJ)
    (h219 : Item219) : Item2115 :=
  item2115_of_two h211 h213 h214 h215 h217 h45 h66 hL3 hU4S
    (item2110Two_of_parts h211 h45 h48 h426 h129 hI hF hON hC) hTGHJ h219
    (item2110One_of_parts h211 h45 h48 h426 h129 hI hF hON hC h23)

end Assembly

end CFSG.RankThree.PartTwo.Sec21.Item2110Res2Proof
