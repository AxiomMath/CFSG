module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434Consequences
public import CFSG.RankThree.PartTwo.Sec19.SimsC198Holds
public import CFSG.RankThree.PartTwo.Sec19.F194Wide3
public import CFSG.RankThree.PartTwo.Sec19.Item19Res4ProofWide3
public import CFSG.RankThree.PartTwo.Sec19.Step197Proof
public import CFSG.RankThree.PartTwo.Sec19.Step198DProof
public import CFSG.RankThree.PartTwo.Sec19.Step1910O2Proof
public import CFSG.RankThree.PartTwo.Sec19.Item195
public import CFSG.RankThree.PartTwo.Sec13.Ronan138SylowSN
public import CFSG.RankThree.PartTwo.Sec19.Ronan1914Leaves
public import CFSG.RankThree.PartTwo.Sec19.Ronan825YAssembly

public section

namespace CFSG.RankThree.PartTwo.Sec19.Ronan1914


theorem step1914_of_leaves316
    (h_Item1730 : CFSG.RankThree.PartTwo.Sec17.Item1730)
    (h_Item316 : CFSG.RankThree.PartTwo.Sec19.Item316) :
    CFSG.RankThree.PartTwo.Sec19.Step1914 := by
  have h_Item131 := CFSG.RankThree.PartTwo.Sec13.rank3II_13_1_holds
  have h_SporadicModels131 := CFSG.RankThree.PartTwo.KFacts.KS14.sporadicModels131
  have h_Item4_44_1 := CFSG.RankThree.PartTwo.Sec4.item4_44_1_holds
  have h_Item181_1 := CFSG.RankThree.PartTwo.Sec18.rank3II_18_1_1_of (h444 := h_Item4_44_1)
  have h_Item181_2 := CFSG.RankThree.PartTwo.Sec18.item181_2_holds
  have h_Item4_5 := CFSG.RankThree.PartTwo.Sec4.rank3II_4_5
  have h_Step196 := CFSG.RankThree.PartTwo.Sec19.step196_of (h45 := h_Item4_5) (h131 := h_Item131)
    (hspor := h_SporadicModels131)
  have h_Item4_8 := CFSG.RankThree.PartTwo.Sec11.Close.closed_sec4Item4_8
  have h_Census198 := CFSG.RankThree.PartTwo.Sec19.census198_holds
  have h_Step198 := CFSG.RankThree.PartTwo.Sec19.step198_of (h131 := h_Item131)
    (hspor := h_SporadicModels131) (h45 := h_Item4_5) (h48 := h_Item4_8) (hC := h_Census198)
  have h_Item4_44_2 := CFSG.RankThree.PartTwo.Sec4.item4_44_2_holds
  have h_Item194UsedWide3 := CFSG.RankThree.PartTwo.Sec19.item194UsedWide3_of_item316
    (h316 := h_Item316)
  have h_Step1910 := CFSG.RankThree.PartTwo.Sec19.step1910_of_wide3 (h194 := h_Item194UsedWide3)
  have h_Step1911 := CFSG.RankThree.PartTwo.Sec19.step1911_of_wide3 (h194 := h_Item194UsedWide3)
  have h_Step1911End := CFSG.RankThree.PartTwo.Sec19.step1911End_of_wide3
    (h194 := h_Item194UsedWide3) (h131 := h_Item131)
  have h_Step197 := CFSG.RankThree.PartTwo.Sec19.step197_of (h4441 := h_Item4_44_1)
    (h4442 := h_Item4_44_2) (h45 := h_Item4_5) (h131 := h_Item131) (h1730 := h_Item1730)
    (hspor := h_SporadicModels131) (h198 := h_Step198) (h1910 := h_Step1910) (h1911 := h_Step1911)
    (h1911E := h_Step1911End)
  have h_Step198D := CFSG.RankThree.PartTwo.Sec19.step198D_of (h197 := h_Step197)
  have h_Seitz199 := CFSG.RankThree.PartTwo.Sec19.RonanSeitz199.seitz199_holds
  have h_Step199 := CFSG.RankThree.PartTwo.Sec19.step199_of (h197 := h_Step197) (h198 := h_Step198)
    (hS := h_Seitz199)
  have h_Step1910O2 := CFSG.RankThree.PartTwo.Sec19.rank3II_19_10_O2_of (h131 := h_Item131)
  have h_Item195 := CFSG.RankThree.PartTwo.Sec19.rank3II_19_5_of (h1730 := h_Item1730)
    (h131 := h_Item131) (hspor := h_SporadicModels131) (h181 := h_Item181_1) (h1812 := h_Item181_2)
    (h196 := h_Step196) (h198 := h_Step198) (h198D := h_Step198D) (h199 := h_Step199)
    (h1910O2 := h_Step1910O2) (h1910 := h_Step1910) (h1911 := h_Step1911) (h1911E := h_Step1911End)
  have h_Item138SylowN := CFSG.RankThree.PartTwo.Sec13.Ronan138SylowSN.item138SylowN_holds
  have h_Item138SN := CFSG.RankThree.PartTwo.Sec13.Ronan138SylowSN.item138SN_holds
  have h_Step1914 := CFSG.RankThree.PartTwo.Sec19.Ronan1914.step1914_of_leaves
    (h_Item1730 := h_Item1730) (h_Item195 := h_Item195) (h_Item138SylowN := h_Item138SylowN)
    (h_Item138SN := h_Item138SN)
  exact h_Step1914

theorem step1918_of_leaves316
    (h_Item1730 : CFSG.RankThree.PartTwo.Sec17.Item1730)
    (h_Item316 : CFSG.RankThree.PartTwo.Sec19.Item316) :
    CFSG.RankThree.PartTwo.Sec19.Step1918 := by
  have h_Item131 := CFSG.RankThree.PartTwo.Sec13.rank3II_13_1_holds
  have h_SporadicModels131 := CFSG.RankThree.PartTwo.KFacts.KS14.sporadicModels131
  have h_SLTwoCenter := CFSG.RankThree.PartTwo.Sec13.slTwoCenter
  have h_Item4_4 := CFSG.RankThree.PartTwo.Sec4.Census.rank3II_4_4_of_griess_noItem41
  have h_Item4_4Types135 := CFSG.RankThree.PartTwo.Sec13.item4_4Types135_of_item4_4
    (h44 := h_Item4_4)
  have h_KS135TwoRankCover := CFSG.RankThree.PartTwo.Sec13.ks135TwoRankCover
  have h_Item4_14_local := CFSG.RankThree.PartTwo.Sec4.Sporadic.rank3II_4_14_local
  have h_Item4_15 := CFSG.RankThree.PartTwo.Sec4.Sporadic.rank3II_4_15
  have h_KS135TwoRank := CFSG.RankThree.PartTwo.Sec13.ks135TwoRank_of_cover
    (hC := h_KS135TwoRankCover) (h414 := h_Item4_14_local) (h415 := h_Item4_15)
  have h_Item135SimpleReduce := CFSG.RankThree.PartTwo.Sec13.item135SimpleReduce_narrow
    (h44 := h_Item4_4Types135) (hK := h_KS135TwoRank) (hspor := h_SporadicModels131)
    (h414 := h_Item4_14_local) (h415 := h_Item4_15)
  have h_Item135SimpleL3 := CFSG.RankThree.PartTwo.Sec13.item135SimpleL3
  have h_Item135Simple := CFSG.RankThree.PartTwo.Sec13.item135Simple_of_steps
    (hR := h_Item135SimpleReduce) (hL3 := h_Item135SimpleL3)
  have h_Item1730HJ := CFSG.RankThree.PartTwo.Sec17.item1730HJ_of_item1730 (h := h_Item1730)
  have h_KS18Mult := CFSG.RankThree.PartTwo.KFacts.KS14.ks18Mult
  have h_KS18A7M22 := CFSG.RankThree.PartTwo.KFacts.KS14.ks18A7M22
  have h_Step1913 := CFSG.RankThree.PartTwo.Sec19.rank3II_19_13_of_kfacts_hj' (h131 := h_Item131)
    (hspor := h_SporadicModels131) (hSLC := h_SLTwoCenter) (h135 := h_Item135Simple)
    (h1730 := h_Item1730HJ) (hmult := h_KS18Mult) (hA7 := h_KS18A7M22)
  have h_Item4_34Sec := CFSG.RankThree.PartTwo.Sec4.item4_34Sec_holds
  have h_Item194UsedWide3 := CFSG.RankThree.PartTwo.Sec19.item194UsedWide3_of_item316
    (h316 := h_Item316)
  have h_Step1917 := CFSG.RankThree.PartTwo.Sec19.Ronan825Y.step1917_of_step1913
    (h1913 := h_Step1913) (h434 := h_Item4_34Sec) (h131 := h_Item131) (h194 := h_Item194UsedWide3)
  have h_Step1918 := CFSG.RankThree.PartTwo.Sec19.step1918_of_step1913_step1917
    (h1913 := h_Step1913) (h1917 := h_Step1917)
  exact h_Step1918

theorem item195_of_leaves
    (h_Item1730 : CFSG.RankThree.PartTwo.Sec17.Item1730)
    (h_Item316 : CFSG.RankThree.PartTwo.Sec19.Item316) :
    CFSG.RankThree.PartTwo.Sec19.Item195 := by
  have h_Item131 := CFSG.RankThree.PartTwo.Sec13.rank3II_13_1_holds
  have h_SporadicModels131 := CFSG.RankThree.PartTwo.KFacts.KS14.sporadicModels131
  have h_Item4_44_1 := CFSG.RankThree.PartTwo.Sec4.item4_44_1_holds
  have h_Item181_1 := CFSG.RankThree.PartTwo.Sec18.rank3II_18_1_1_of (h444 := h_Item4_44_1)
  have h_Item181_2 := CFSG.RankThree.PartTwo.Sec18.item181_2_holds
  have h_Item4_5 := CFSG.RankThree.PartTwo.Sec4.rank3II_4_5
  have h_Step196 := CFSG.RankThree.PartTwo.Sec19.step196_of (h45 := h_Item4_5) (h131 := h_Item131)
    (hspor := h_SporadicModels131)
  have h_Item4_8 := CFSG.RankThree.PartTwo.Sec11.Close.closed_sec4Item4_8
  have h_Census198 := CFSG.RankThree.PartTwo.Sec19.census198_holds
  have h_Step198 := CFSG.RankThree.PartTwo.Sec19.step198_of (h131 := h_Item131)
    (hspor := h_SporadicModels131) (h45 := h_Item4_5) (h48 := h_Item4_8) (hC := h_Census198)
  have h_Item4_44_2 := CFSG.RankThree.PartTwo.Sec4.item4_44_2_holds
  have h_Item194UsedWide3 := CFSG.RankThree.PartTwo.Sec19.item194UsedWide3_of_item316
    (h316 := h_Item316)
  have h_Step1910 := CFSG.RankThree.PartTwo.Sec19.step1910_of_wide3 (h194 := h_Item194UsedWide3)
  have h_Step1911 := CFSG.RankThree.PartTwo.Sec19.step1911_of_wide3 (h194 := h_Item194UsedWide3)
  have h_Step1911End := CFSG.RankThree.PartTwo.Sec19.step1911End_of_wide3
    (h194 := h_Item194UsedWide3) (h131 := h_Item131)
  have h_Step197 := CFSG.RankThree.PartTwo.Sec19.step197_of (h4441 := h_Item4_44_1)
    (h4442 := h_Item4_44_2) (h45 := h_Item4_5) (h131 := h_Item131) (h1730 := h_Item1730)
    (hspor := h_SporadicModels131) (h198 := h_Step198) (h1910 := h_Step1910) (h1911 := h_Step1911)
    (h1911E := h_Step1911End)
  have h_Step198D := CFSG.RankThree.PartTwo.Sec19.step198D_of (h197 := h_Step197)
  have h_Seitz199 := CFSG.RankThree.PartTwo.Sec19.RonanSeitz199.seitz199_holds
  have h_Step199 := CFSG.RankThree.PartTwo.Sec19.step199_of (h197 := h_Step197) (h198 := h_Step198)
    (hS := h_Seitz199)
  have h_Step1910O2 := CFSG.RankThree.PartTwo.Sec19.rank3II_19_10_O2_of (h131 := h_Item131)
  have h_Item195 := CFSG.RankThree.PartTwo.Sec19.rank3II_19_5_of (h1730 := h_Item1730)
    (h131 := h_Item131) (hspor := h_SporadicModels131) (h181 := h_Item181_1) (h1812 := h_Item181_2)
    (h196 := h_Step196) (h198 := h_Step198) (h198D := h_Step198D) (h199 := h_Step199)
    (h1910O2 := h_Step1910O2) (h1910 := h_Step1910) (h1911 := h_Step1911) (h1911E := h_Step1911End)
  exact h_Item195

end CFSG.RankThree.PartTwo.Sec19.Ronan1914
