module

public import CFSG.RankThree.PartTwo.Sec13.KS135TwoRankCover
public import CFSG.RankThree.PartTwo.Sec13.Item135Narrow
public import CFSG.RankThree.PartTwo.Sec13.Item135SimpleL3Proof
public import CFSG.RankThree.PartTwo.KFacts.KS18MultProof
public import CFSG.RankThree.PartTwo.KFacts.KS18A7M22Proof
public import CFSG.RankThree.PartTwo.Sec13.Item135SimpleStep1913
public import CFSG.RankThree.PartTwo.Sec19.RonanSeitzL3Pi
public import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
public import CFSG.RankThree.PartTwo.Sec19.Step1914MoreSProofL34Cartan
public import CFSG.RankThree.PartTwo.Sec4.Item422Holds
public import CFSG.RankThree.PartTwo.Sec13.Item13Final
public import CFSG.RankThree.PartTwo.Sec13.Item134Unconditional
public import CFSG.RankThree.PartTwo.Sec13.Ronan137Holds
public import CFSG.RankThree.PartTwo.Sec19.Step1914MoreSProofM12Gen

public section

namespace CFSG.RankThree.PartTwo.Sec19.Ronan1914

theorem step1914_of_leaves
    (h_Item1730 : CFSG.RankThree.PartTwo.Sec17.Item1730)
    (h_Item195 : CFSG.RankThree.PartTwo.Sec19.Item195)
    (h_Item138SylowN : CFSG.RankThree.PartTwo.Sec13.Item138SylowN)
    (h_Item138SN : CFSG.RankThree.PartTwo.Sec13.Item138SN) :
    CFSG.RankThree.PartTwo.Sec19.Step1914 := by
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
  have h_SeitzL3Pi := CFSG.RankThree.PartTwo.Sec19.RonanSeitzL3Pi.seitzL3Pi_holds
  have h_Step1914Tri := CFSG.RankThree.PartTwo.Sec19.rank3II_19_14Tri_of (h1913 := h_Step1913)
    (hS := h_SeitzL3Pi)
  have h_Step1914MoreSL34 := CFSG.RankThree.PartTwo.Sec19.step1914MoreSL34_of (h131 := h_Item131)
    (htri := h_Step1914Tri) (h195 := h_Item195) (hSyl := h_Item138SylowN) (hS := h_Item138SN)
  have h_Item4_22 := CFSG.RankThree.PartTwo.item4_22_holds
  have h_Item4_5 := CFSG.RankThree.PartTwo.Sec4.rank3II_4_5
  have h_Item132 := CFSG.RankThree.PartTwo.Sec13.rank3II_13_2_of (h131 := h_Item131)
    (h422 := h_Item4_22) (h45 := h_Item4_5)
  have h_Item133 := CFSG.RankThree.PartTwo.Sec13.rank3II_13_3_of (h131 := h_Item131)
    (h422 := h_Item4_22) (h45 := h_Item4_5)
  have h_Item134 := CFSG.RankThree.PartTwo.item134_holds
  have h_Item4_8 := CFSG.RankThree.PartTwo.Sec11.Close.closed_sec4Item4_8
  have h_Item13SetupAt := CFSG.RankThree.PartTwo.Sec13.item13SetupAt_of (h422 := h_Item4_22)
    (h45 := h_Item4_5)
  have h_Item13Setup := CFSG.RankThree.PartTwo.Late.item13Setup_of (hsetAt := h_Item13SetupAt)
  have h_Item137InvertPGL := CFSG.RankThree.PartTwo.Sec13.Ronan137H.item137InvertPGL_holds
  have h_Step1914MoreSM12 := CFSG.RankThree.PartTwo.Sec19.step1914MoreSM12_of
    (htri := h_Step1914Tri) (h131 := h_Item131) (h132 := h_Item132) (h133 := h_Item133)
    (h134 := h_Item134) (h48 := h_Item4_8) (h13S := h_Item13Setup) (hPGL := h_Item137InvertPGL)
    (h195 := h_Item195)
  have h_Step1914More := CFSG.RankThree.PartTwo.Sec19.step1914More_of (htri := h_Step1914Tri)
    (h131 := h_Item131) (hSL := h_Step1914MoreSL34) (hSM := h_Step1914MoreSM12)
  have h_Step1914 := CFSG.RankThree.PartTwo.Sec19.rank3II_19_14_of_more (h1913 := h_Step1913)
    (hS := h_SeitzL3Pi) (hmore := h_Step1914More)
  exact h_Step1914

end CFSG.RankThree.PartTwo.Sec19.Ronan1914
