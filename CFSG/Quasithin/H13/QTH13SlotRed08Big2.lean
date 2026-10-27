module

public import CFSG.GH74.M12.AscTheorem1
public import CFSG.Quasithin.Background.E6TwelveProved
public import CFSG.Quasithin.H13.NQCatKG68All
public import CFSG.Quasithin.H13.E22CHolds
public import CFSG.Quasithin.H13.U3LCE
public import CFSG.Quasithin.Vol2.Asc94.He42Holds
public import CFSG.Quasithin.Vol2.Asc94.HeOrderHolds
public import CFSG.Quasithin.Vol2.Ch11SecOE3K
public import CFSG.Quasithin.Vol2.Ch12Sec1Final
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1HeJ
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1NmH
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem18RankTop
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem19
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem19Top
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem20TrB
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem22W
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem23D
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem25K
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem25T
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem25X
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem26A8Fix
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem7UW
public import CFSG.Quasithin.Vol2.Ch12Sec2Prop27Three
public import CFSG.Quasithin.Vol2.Ch12Sec2Thm12111
public import CFSG.Quasithin.Vol2.Ch1Sec3Lem139Holds
public import CFSG.Quasithin.Vol2.Ch3Sec3FrontierA
public import CFSG.Quasithin.Vol2.Ch3T313C
public import CFSG.Quasithin.Vol2.Ch3T326H2ShapeHolds
public import CFSG.Quasithin.Vol2.Ch4Sec4W4414F
public import CFSG.Quasithin.Vol2.Ch7Input755Strong
public import CFSG.Quasithin.Vol2.Ch7TableM22Hat
public import CFSG.Quasithin.Vol2.GoldschmidtTDOutMain
public import CFSG.Quasithin.Vol2.KGFactHeInspE64
public import CFSG.Quasithin.Vol2.KGFactHeInspRank
public import CFSG.Quasithin.Vol2.KGFactHeInspRu
public import CFSG.Yardstones.M64f425cd8476.Definitions
public import CFSG.Quasithin.H13.QTH13SlotBig
public import CFSG.Quasithin.MS93.C134L32CorrMHolds
public import CFSG.Quasithin.Vol2.Ch10Reselect.WWire10AInputs
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem4C9W
public import CFSG.Milestones.ASVolI.C31.J4KWHolds
public import CFSG.Quasithin.Recognition.G23Ctx.Assembly
public import CFSG.Quasithin.H13.QTH13Slot11C132

public section

namespace CFSG.Yardstones.M64f425cd8476

theorem ys08_of_slots_big2
    (h01 : Chapter3Theorems) (h02 : Chapter4Theorems) (h04 : CFSG.Quasithin.H13.Stmt6_2_20)
    (h05 : Theorem701Steps) (h06 : Section82Steps) (h07 : CFSG.Quasithin.H13.Stmt11_0_1)
    (h10 : CFSG.Quasithin.H13.InputAS91) :
    Chapter12Section2Inputs := by
  have h132 : CFSG.Quasithin.ASInputs.AS_C_1_32 := CFSG.Quasithin.H13.asC132_holds
  have h12 : LiteratureRecognitionInputs :=
    ⟨CFSG.ASVolI.burnsideJ4KW_twoLocals_holds, CFSG.Quasithin.G23Type.Ctx.statementI45_holds⟩
  have p_E22StatementC := CFSG.Quasithin.H13.e22StatementC_holds
  have p_Stmt3_3_1 := h01.stmt3_3_1
  have p_Stmt4_4_3Orbit := h02.stmt4_4_3
  have p_TheoremC58 := CFSG.Quasithin.theoremC58_proved
  have p_AS317Sylow := CFSG.Quasithin.as317Sylow_proved
  have p_Stmt4_4_14 := CFSG.Quasithin.H13.Ch4.stmt4_4_14_of_steps p_Stmt4_4_3Orbit p_E22StatementC p_TheoremC58 p_AS317Sylow
  have p_Theorem316Statement := CFSG.Quasithin.Ch3T316W.theorem316Statement_holds
  have p_D310C0 := CFSG.Quasithin.H13.d310C0_holds
  have p_TmpL6_3_2_2_eight := CFSG.Quasithin.Vol2.Ch10.tmpL6_3_2_2_eight_proved
  have p_Stmt3_2_3 := CFSG.Quasithin.H13.stmt3_2_3_proved
  have p_TmpL6_3_2_2_two := CFSG.Quasithin.Vol2.Ch10.tmpL6_3_2_2_two_of p_TmpL6_3_2_2_eight p_Stmt3_2_3
  have p_TmpL6_3_2_2_four := CFSG.Quasithin.Vol2.Ch11.tmpL6_3_2_2_four_of p_TmpL6_3_2_2_two
  have p_TmpL6_3_2_2_six := CFSG.Quasithin.Vol2.Ch11.tmpL6_3_2_2_six_of p_TheoremC58 p_AS317Sylow p_Stmt3_3_1 p_TmpL6_3_2_2_eight p_TmpL6_3_2_2_four
  have p_AsB56 := CFSG.Quasithin.asB56_holds
  have p_Stmt3_2_5 := CFSG.Quasithin.H13.stmt3_2_5_of_c0 p_Theorem316Statement p_D310C0 p_Stmt3_3_1 p_TmpL6_3_2_2_two p_TmpL6_3_2_2_eight p_TmpL6_3_2_2_four p_TmpL6_3_2_2_six p_AsB56
  have p_Stmt7_0_1_shapeC := CFSG.Quasithin.H13.stmt7_0_1_shapeC_holds
  have p_Stmt7_2_1_M22Hat := CFSG.Quasithin.H13.stmt7_2_1_M22Hat
  have p_Stmt3_2_6C := CFSG.Quasithin.H13.T326.stmt3_2_6C_of_stmt331 p_Stmt3_3_1
  have p_Input7_5_5 := CFSG.Quasithin.H13.input7_5_5_of_stmt3_2 p_Stmt3_2_5 p_Stmt3_2_6C
  have p_AS_E_6_12 := Quasithin.E6.as_E_6_12_proved Quasithin.H13.KG68.e68ComponentFacts_holds
  have p_OutTwoNilpotentFact := CFSG.Quasithin.H13.outTwoNilpotentFact_holds
  have p_SporadicSylowCenterCyclic := CFSG.Quasithin.H13.KG68.sporadicSylowCenterCyclic_holds
  have p_TrialityTwoSylowCenterCyclic := CFSG.Quasithin.H13.KG68.trialityTwoSylowCenterCyclic_holds
  have p_TitsSylowCenterCyclic := CFSG.Quasithin.H13.KG68.titsSylowCenterCyclic_holds
  have p_AS_C_1_32 := h132
  have p_ASC27Statement := CFSG.Quasithin.asc27Statement_of_c132 p_AS_C_1_32
  have p_ASC24One := CFSG.Quasithin.H13.U3.asc24One_holds
  have p_CorrBig := CFSG.Quasithin.H13.SlotLeaves.burnsideC134w_corrBig_holds
  have p_C134L32CorrM := CFSG.Quasithin.MS93.c134L32CorrM_holds
  have p_J4TwoLocalsKW := h12.j4TwoLocals
  have p_ASC48Statement := CFSG.Quasithin.H13.SlotLeaves.asc48Statement_forall_of_big p_AS_C_1_32 p_CorrBig p_J4TwoLocalsKW
  have p_Stmt8_2_13 := h06.stmt8_2_13
  have p_Stmt8_2_13_cocode := CFSG.Quasithin.H13.stmt8_2_13_cocode_of p_Stmt8_2_13
  have p_Stmt8_2_10 := h06.stmt8_2_10
  have p_Stmt8_2_12 := h06.stmt8_2_12
  have p_Stmt8_2_14_fusion := h06.stmt8_2_14_fusion
  have p_InputAS91 := h10
  have p_Stmt8_2_14 := CFSG.Quasithin.H13.stmt8_2_14_of p_Stmt8_2_10 p_Stmt8_2_12 p_Stmt8_2_13 p_Stmt8_2_14_fusion p_InputAS91
  have p_Stmt8_3_1 := h05.stmt8_3_1
  have p_Stmt9_omegaPlusA := h05.stmt9_omegaPlusA
  have p_Stmt4_2_13FF := h02.stmt4_2_13
  have p_Stmt10_0_1 := CFSG.Quasithin.Vol2.Ch10.stmt10_0_1_of_inputsAW p_E22StatementC p_Stmt3_3_1 p_Stmt4_4_14 p_TheoremC58 p_AS317Sylow p_Stmt3_2_5 p_Stmt7_0_1_shapeC p_Stmt7_2_1_M22Hat p_Input7_5_5 p_AS_E_6_12 p_Stmt4_4_3Orbit p_OutTwoNilpotentFact p_SporadicSylowCenterCyclic p_TrialityTwoSylowCenterCyclic p_TitsSylowCenterCyclic p_ASC27Statement p_ASC24One p_C134L32CorrM p_ASC48Statement p_Stmt8_2_13_cocode p_Stmt8_2_14 p_Stmt8_3_1 p_Theorem316Statement p_Stmt9_omegaPlusA p_Stmt4_2_13FF
  have p_ASC19Statement := CFSG.Quasithin.asc19Statement_holds
  have p_HeInspRankEight := CFSG.Quasithin.H13.KGRank.heInspRankEight_holds
  have p_HeInspE64 := CFSG.Quasithin.H13.KGE64.heInspE64_holds
  have p_HeInspRu := CFSG.Quasithin.H13.KGInsp.heInspRu_holds
  have p_KGJ4SylowOvergroups := CFSG.Quasithin.H13.kgJ4SylowOvergroups_holds
  have p_HeInspJ4 := CFSG.Quasithin.H13.KGInsp.heInspJ4_of p_KGJ4SylowOvergroups
  have p_Lem1211HeInsp := CFSG.Quasithin.H13.Sec1211He.lem1211HeInsp_of_remaining p_HeInspRankEight p_HeInspE64 p_HeInspRu p_HeInspJ4
  have p_Lem1211NormalLin := CFSG.Quasithin.H13.lem1211NormalLin_holds
  have p_Stmt11_0_1 := h07
  have p_Stmt3_2_8 := CFSG.Quasithin.H13.stmt3_2_8_proved
  have p_Stmt3_2_9C := CFSG.Quasithin.H13.stmt3_2_9C_of p_Stmt3_2_5 p_Theorem316Statement
  have p_Lemma128Two := CFSG.Quasithin.H13.lemma128Two_proved
  have p_Lemma128Four := CFSG.Quasithin.H13.lemma128Four_proved
  have p_Lemma139L42Inner := CFSG.Quasithin.H13.lemma139L42Inner_proved
  have p_Lemma139A5Inner := Quasithin.L139A5.lemma139A5Inner_of
      (Quasithin.a37ForSQTK_of_cat QuasithinUnique.Vol2Native.a37ForSQTKCat_proved)
  have p_A38ForSQTKCat := CFSG.Quasithin.H13.Frontier331.a38Cat
  have p_Lem1214Step := CFSG.Quasithin.H13.lem1214Step_of_cW p_Stmt3_3_1 p_Stmt10_0_1 p_Stmt11_0_1 p_Stmt3_2_3 p_Stmt3_2_5 p_Stmt3_2_8 p_Stmt3_2_9C p_C134L32CorrM p_Lemma128Two p_Lemma128Four p_Lemma139L42Inner p_Lemma139A5Inner p_A38ForSQTKCat
  have p_Stmt12_1_11 := CFSG.Quasithin.H13.stmt12_1_11_of_remaining p_Stmt10_0_1 p_Stmt3_3_1 p_Stmt4_4_3Orbit p_E22StatementC p_ASC19Statement p_ASC27Statement p_Lem1211HeInsp p_Lem1211NormalLin p_Lem1214Step
  have p_Stmt6_2_20 := h04
  have p_Stmt7_0_1A := CFSG.Quasithin.H13.Ch9.stmt7_0_1A_of_rowsW p_E22StatementC p_Stmt3_3_1 p_Stmt4_4_14 p_TheoremC58 p_AS317Sylow p_Stmt3_2_5 p_Stmt7_0_1_shapeC p_Stmt7_2_1_M22Hat p_Input7_5_5 p_AS_E_6_12 p_Stmt4_4_3Orbit p_OutTwoNilpotentFact p_SporadicSylowCenterCyclic p_TrialityTwoSylowCenterCyclic p_TitsSylowCenterCyclic p_ASC27Statement p_ASC24One p_C134L32CorrM p_ASC48Statement p_Stmt8_2_13_cocode p_Stmt8_2_14 p_Stmt8_3_1 p_Theorem316Statement p_Stmt9_omegaPlusA
  have p_Stmt7_0_1 := CFSG.Quasithin.H13.stmt7_0_1_of_A p_Stmt7_0_1A
  have p_Stmt12_2_2 := CFSG.Quasithin.H13.stmt12_2_2_of_12111 p_Stmt10_0_1 p_Stmt3_2_5 p_Stmt6_2_20 p_Stmt7_0_1 p_Stmt11_0_1 p_Stmt12_1_11
  have p_Stmt3_2_2_eight := CFSG.Quasithin.H13.stmt3_2_2_eight_proved
  have p_AsB51 := CFSG.Quasithin.B5.asB51_holds
  have p_Lem12216A8VvComm := CFSG.Quasithin.H13.lem12216A8VvComm_of p_Stmt12_2_2 p_Stmt3_2_3 p_Stmt3_2_2_eight p_AsB51
  have p_Lem12216A8VvFix := CFSG.Quasithin.H13.lem12216A8VvFix_of p_Stmt12_2_2 p_Stmt3_2_2_eight
  have p_Lem12216A8Zv := CFSG.Quasithin.H13.lem12216A8Zv_of p_Lem12216A8VvComm p_Lem12216A8VvFix
  have p_Stmt12_2_16 := CFSG.Quasithin.H13.stmt12_2_16_of_A8Zv p_Stmt12_2_2 p_Stmt3_3_1 p_Stmt3_2_3 p_Lem12216A8Zv
  have p_A37ForSQTK := CFSG.Quasithin.a37ForSQTK_proved
  have p_A37ForSQTKCat := CFSG.QuasithinUnique.Vol2Native.a37ForSQTKCat_proved
  have p_A36ForSQTK := CFSG.Quasithin.H13.VolI.a36ForSQTK_holds
  have p_StmtFSUChoice := CFSG.Quasithin.Vol2.Ch10.stmtFSUChoice_of_a36 p_Stmt3_2_3 p_A36ForSQTK
  have p_NoOddLinearThreeLStarF := CFSG.Quasithin.Vol2.Ch11.OE3.noOddLinear_of p_A37ForSQTKCat p_A38ForSQTKCat p_StmtFSUChoice p_Stmt7_0_1
  have p_UniqueThreeCaseModelReduction := CFSG.Quasithin.H13.U3.uniqueThreeCaseModelReduction_holds
  have p_Lemma3_2_13Consumed := CFSG.Quasithin.H13.lemma3_2_13Consumed_of p_Theorem316Statement p_UniqueThreeCaseModelReduction
  have p_Lemma3_2_14HomocyclicConsumed := CFSG.Quasithin.Vol2.Ch11.OE4.lemma3_2_14HomocyclicConsumed_of p_Theorem316Statement p_UniqueThreeCaseModelReduction
  have p_A312ListFactsCat := CFSG.Quasithin.Vol2.Ch10.a312ListFactsCat_holds
  have p_Stmt3_2_14 := CFSG.Quasithin.H13.NQBlock.stmt3_2_14_of p_NoOddLinearThreeLStarF p_Lemma3_2_13Consumed p_Lemma3_2_14HomocyclicConsumed p_A312ListFactsCat
  have p_Stmt12_2_7 := CFSG.Quasithin.H13.stmt12_2_7_of_unique p_Stmt3_3_1 p_Stmt12_2_2 p_Stmt6_2_20 p_A37ForSQTK p_Stmt3_2_14
  have p_Stmt12_2_18 := CFSG.Quasithin.H13.stmt12_2_18_of_A8Zv p_Stmt3_3_1 p_Stmt12_2_2 p_Stmt3_2_3 p_Lem12216A8Zv p_Stmt12_2_7
  have p_Lem12219Solvable := CFSG.Quasithin.H13.lem12219Solvable_of p_Stmt3_3_1 p_Stmt12_2_2 p_Stmt12_2_16 p_Stmt12_2_18 p_Stmt12_2_7
  have p_AS_I_6_2_twoCases := CFSG.Quasithin.I62.as_I_6_2_twoCases_holds
  have p_Lem12220Choice := CFSG.Quasithin.H13.lem12220Choice_of_coprime p_Stmt3_3_1 p_Stmt12_2_2 p_Stmt3_2_5 p_Stmt12_2_16 p_Stmt12_2_18 p_AS_I_6_2_twoCases
  have p_Lem12220PickFull := CFSG.Quasithin.H13.lem12220PickFull_of p_Stmt3_3_1 p_Lem12220Choice
  have p_Lem12220Pick := CFSG.Quasithin.H13.lem12220Pick_of_full p_Lem12220PickFull
  have p_Lem12220Transv := CFSG.Quasithin.H13.lem12220Transv_of p_Stmt12_2_2
  have p_Stmt12_2_20 := CFSG.Quasithin.H13.stmt12_2_20_of_solv p_Stmt12_2_2 p_Stmt3_2_3 p_Lem12219Solvable p_Lem12220Pick p_Lem12220Transv
  have p_KGBorelOvergroupThree := CFSG.Quasithin.H13.kgBorelOvergroupThree
  have p_Lem12223ExtraL32 := CFSG.Quasithin.H13.lem12223ExtraL32_proved p_Stmt3_3_1 p_Stmt12_2_2
  have p_Lem12223ExtraN45 := CFSG.Quasithin.H13.Lem22.lem12223ExtraN45_of p_Stmt3_3_1 p_Stmt12_2_2
  have p_Lem12223Extra := CFSG.Quasithin.H13.lem12223Extra_of p_Stmt3_3_1 p_Stmt12_2_2 p_Lem12223ExtraL32 p_Lem12223ExtraN45
  have p_Lem12222Frattini := CFSG.Quasithin.H13.lem12222Frattini_of_extra p_Stmt3_3_1 p_Stmt12_2_2 p_Stmt12_2_16 p_KGBorelOvergroupThree p_Lem12223Extra
  have p_Lem12221_23 := CFSG.Quasithin.H13.lem12221_23_of_frattini p_Stmt3_3_1 p_Stmt12_2_2 p_Stmt3_2_5 p_Stmt12_2_16 p_Stmt12_2_18 p_AS_I_6_2_twoCases p_Lem12222Frattini
  have p_Lem12224Block := CFSG.Quasithin.H13.lem12224Block_of p_Stmt12_2_2
  have p_Stmt12_2_24_config := CFSG.Quasithin.H13.stmt12_2_24_config_of_solv p_Lem12219Solvable p_Stmt12_2_20 p_Lem12221_23 p_Lem12224Block
  have p_A38ForSQTK := CFSG.Quasithin.a38ForSQTK_proved
  have p_A39ForSQTK := CFSG.Quasithin.a39ForSQTK_proved
  have p_A312ForSQTK := CFSG.Quasithin.H13.a312ForSQTK_proved
  have p_Lem12225YNormal := CFSG.Quasithin.H13.lem12225YNormal_of p_Stmt3_3_1 p_Stmt12_2_2 p_Stmt3_2_3 p_Stmt12_2_16 p_Stmt12_2_20 p_A36ForSQTK p_A37ForSQTK p_A38ForSQTK p_A39ForSQTK p_A312ForSQTK
  have p_Lem12225CTL3 := CFSG.Quasithin.H13.lem12225CTL3_of p_Stmt3_3_1 p_Stmt12_2_2 p_Stmt3_2_3 p_Stmt12_2_16 p_Stmt12_2_20
  have p_Lem12225N5 := CFSG.Quasithin.H13.lem12225N5_of p_Stmt3_3_1 p_Stmt12_2_2 p_Stmt3_2_3 p_Stmt12_2_16 p_Stmt12_2_20 p_Lem12225YNormal
  have p_Lem12226Split := CFSG.Quasithin.H13.lem12226Split_of p_Stmt3_3_1 p_Stmt12_2_2 p_Stmt3_2_3 p_Stmt12_2_16 p_Stmt12_2_20 p_Lem12225YNormal
  have p_Stmt12_2_25_26_of_config := CFSG.Quasithin.H13.stmt12_2_25_26_of_config_of p_Stmt3_3_1 p_Stmt12_2_2 p_Stmt3_2_3 p_Stmt12_2_16 p_Stmt12_2_20 p_Lem12225YNormal p_Lem12225CTL3 p_Lem12225N5 p_Lem12226Split
  have p_He_order := CFSG.Quasithin.A94.he_order_holds
  have p_Asc94_M24He_L52TypeK := CFSG.Quasithin.A94.asc94K_of_he_order p_He_order
  have p_S_Asc03_Theorem1 := CFSG.GH74.M12.s_asc03_theorem1
  have p_Stmt12_2_6 := CFSG.Quasithin.H13.stmt12_2_6_of p_Stmt12_2_2 p_Stmt3_2_3
  have p_Stmt12_2_27 := CFSG.Quasithin.H13.stmt12_2_27_of p_Asc94_M24He_L52TypeK p_S_Asc03_Theorem1 p_Stmt12_2_6
  have p_Stmt12_2_13 := CFSG.Quasithin.H13.stmt12_2_13_of_config p_Stmt12_2_24_config p_Stmt12_2_25_26_of_config p_Stmt12_2_27
  exact ⟨p_Stmt12_1_11, p_Stmt12_2_13⟩

end CFSG.Yardstones.M64f425cd8476

end
