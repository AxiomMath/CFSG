module

public import CFSG.RankThree.PartTwo.Sec6.Item611FixProofMain
public import CFSG.RankThree.PartTwo.Sec6.Item611FixProofE81
public import CFSG.RankThree.PartTwo.Sec6.Item611Res3Proof
public import CFSG.RankThree.PartTwo.Sec6.Item611Res4ProofE81

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4

theorem item6_11_1Main_of_res3Fix
    (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h49 : Sec4.Item4_9)
    (hKf : KFacts.KS6OuterIndex) (h41 : Sec4.Item4_1LargePrime)
    (h413 : Sec4.Item4_13_forwardFix) (h641 : Item6_4_1) (hU : Item611UPlusCent)
    (hF : Item611FieldL2S) (hKE : KS611E81Inv) (hEI : Item611E81Inv) : Item6_11_1Main :=
  item6_11_1Main_of_res2Fix h45 h41 h413 h641 (item611UPlusOut_ofFix h45 h48 h49 hKf h41 h413 hU)
    (item611ChooseMinus_holdsFix h45 h48 h49 hKf h41 h413) (item611FieldL2T_of hF)
    item611NotG2T_holds (item611NotE81T_of (item611E81Lift_of h45 hKE) hEI)

theorem item6_11_1Main_of_res4Fix
    (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h49 : Sec4.Item4_9)
    (hKf : KFacts.KS6OuterIndex) (h41 : Sec4.Item4_1LargePrime)
    (h413 : Sec4.Item4_13_forwardFix) (h641 : Item6_4_1) (hK : KS611CentChar3)
    (hF : Item611FieldL2S) (hEI : Item611E81Inv) : Item6_11_1Main :=
  item6_11_1Main_of_res3Fix h45 h48 h49 hKf h41 h413 h641
    (item611UPlusCent_of_res4Fix h45 h41 h413 hK) hF kS611E81Inv_holds hEI

theorem item611E81Inv_of_threeLocalFix
    (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h49 : Sec4.Item4_9)
    (hKf : KFacts.KS6OuterIndex) (h41 : Sec4.Item4_1LargePrime)
    (h413 : Sec4.Item4_13_forwardFix) (hU : KCentCharThreeU43)
    (hV : Item611E81V) (hCore : Item611E81Core) : Item611E81Inv :=
  item611E81Inv_of_res5Fix h45 h48 h49 hKf h41 h413
    (item611UPlusCent_of_threeLocalFix h45 h41 h413 kCentCharThreeL43_holds hU) hV hCore

theorem item6_11_1Main_of_res5Fix
    (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h49 : Sec4.Item4_9)
    (hKf : KFacts.KS6OuterIndex) (h41 : Sec4.Item4_1LargePrime)
    (h413 : Sec4.Item4_13_forwardFix) (h641 : Item6_4_1) (hU : KCentCharThreeU43)
    (hM : Item611FieldL2Max) (hV : Item611E81V)
    (hCore : Item611E81Core) : Item6_11_1Main :=
  item6_11_1Main_of_res4Fix h45 h48 h49 hKf h41 h413 h641 (ks611CentChar3_of_u43 hU)
    (item611FieldL2S_of_max hM) (item611E81Inv_of_threeLocalFix h45 h48 h49 hKf h41 h413 hU hV
      hCore)

theorem item6_11_1_of_res5Fix
    (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h49 : Sec4.Item4_9)
    (hKf : KFacts.KS6OuterIndex) (h41 : Sec4.Item4_1LargePrime)
    (h413 : Sec4.Item4_13_forwardFix) (h641 : Item6_4_1) (hU : KCentCharThreeU43)
    (hM : Item611FieldL2Max) (hV : Item611E81V)
    (hCore : Item611E81Core) : Item6_11_1 :=
  item6_11_1_of_used h45 h48 h49 hKf h641
    (item6_11_1Main_of_res5Fix h45 h48 h49 hKf h41 h413 h641 hU hM hV hCore)

end CFSG.RankThree.PartTwo.Sec6
