module

public import CFSG.RankThree.S4Free.StellmacherSzAllProved
public import CFSG.RankThree.PartTwo.Sec15.Ronan154BigMem
public import CFSG.RankThree.PartTwo.Sec15.Ronan154BigY4
public import CFSG.RankThree.PartTwo.Sec15.Ronan154Big159
public import CFSG.RankThree.PartTwo.Sec15.Item156RDischarge
public import CFSG.RankThree.PartTwo.Sec15.Sylow155E0Switch
public import CFSG.RankThree.PartTwo.Sec15.Sylow155E0Step
public import CFSG.RankThree.PartTwo.J2Residue.KJFixHolds
public import CFSG.RankThree.PartTwo.J2Residue.KJSplitH2
public import CFSG.RankThree.PartTwo.J2Residue.KJCoverHolds
public import CFSG.RankThree.PartTwo.Sec15.Wales154KL3a
public import CFSG.RankThree.PartTwo.Sec15.Wales154KL3c
public import CFSG.RankThree.PartTwo.Sec15.Gagen1515FpfRBoundOff
public import CFSG.RankThree.PartTwo.Sec14.ONCoverProofCent
public import CFSG.RankThree.PartTwo.Sec15.Liebeck1515B
public import CFSG.RankThree.PartTwo.Sec15.KL3FactsProofL325
public import CFSG.RankThree.PartTwo.Sec15.KL3Sub3ProofMain
public import CFSG.RankThree.PartTwo.Sec15.Item15Res9ProofTL
public import CFSG.RankThree.PartTwo.Sec15.KL3Sub2ProofNorm
public import CFSG.RankThree.PartTwo.Sec15.Item15Res9ProofY0
public import CFSG.RankThree.PartTwo.Sec15.KL3FactsProofHess
public import CFSG.RankThree.PartTwo.Sec15.Gagen1521TMain
public import CFSG.RankThree.PartTwo.Sec15.Gagen1521Route
public import CFSG.RankThree.PartTwo.Sec15.Gagen1521U
public import CFSG.RankThree.PartTwo.Sec15.Item1520StepsProofU
public import CFSG.RankThree.PartTwo.Sec15.ResGapProofL34
public import CFSG.RankThree.PartTwo.Sec15.Sylow1523NormTwo
public import CFSG.RankThree.PartTwo.Sec16.Kcd166.KcdFinal
public import CFSG.RankThree.PartTwo.J2Residue.KG1Holds
public import CFSG.RankThree.PartTwo.Sec16.Item166KdLeafKBeta
public import CFSG.RankThree.PartTwo.Sec16.Ronan166KCommD
public import CFSG.RankThree.PartTwo.Sec17.Ronan17NoPGL
public import CFSG.RankThree.PartTwo.Sec17.Item1712Holds
public import CFSG.RankThree.PartTwo.Sec17.Item17Res14ProofInner
public import CFSG.RankThree.PartTwo.Sec14.Ronan143Q174Route
public import CFSG.RankThree.PartTwo.Sec17.Ronan1712Q8Route

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan143Q

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Sec17

@[expose] def RouteHostJ2Small : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (b : G) (Lb : Subgroup G),
    CFSG.RankThree.PartTwo.Sec15.Sec15R G A b Lb →
    (CFSG.RankThree.PartTwo.Sec13.omegaA A).ncard ≤ 3 →
    Nonempty (↥Lb ⧸ CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 ↥Lb ≃*
      CFSG.Blueprint.NativeSporadic.J2) →
    CFSG.RankThree.PartTwo.Sec15.Step155HostE0W A b Lb

@[expose] def RouteHostGood : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (b : G) (Lb : Subgroup G),
    CFSG.RankThree.PartTwo.Sec15.Sec15R G A b Lb →
    (CFSG.RankThree.PartTwo.Sec13.omegaA A).ncard ≤ 9 →
    ¬ CFSG.RankThree.PartTwo.Sec8.IsZ3PGLThreePi (CFSG.RankThree.PartTwo.Sec13.lBarA b Lb A) →
    IsEmpty (↥Lb ⧸ CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 ↥Lb ≃*
      CFSG.Blueprint.NativeSporadic.M12) →
    IsEmpty (↥Lb ⧸ CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 ↥Lb ≃*
      CFSG.Blueprint.NativeSporadic.J2) →
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers b : Set G) →
    CFSG.RankThree.PartTwo.Sec15.Step155HostE0W A b Lb

theorem item1730_of_routeS16_leaves5
    (h_Item316 : Sec19.Item316) (h_Item3_10 : Sec6.Item3_10)
    (h_RouteHostJ2Small : RouteHostJ2Small) (h_RouteHostGood : RouteHostGood) :
    Item1730 := by
  have h_Item131 := CFSG.RankThree.PartTwo.Sec13.rank3II_13_1_holds
  have h_Item134 := CFSG.RankThree.PartTwo.item134_holds
  have h_Item4_8 := CFSG.RankThree.PartTwo.Sec11.Close.closed_sec4Item4_8
  have h_Item4_22 := CFSG.RankThree.PartTwo.item4_22_holds
  have h_Item4_5 := CFSG.RankThree.PartTwo.Sec4.rank3II_4_5
  have h_SporadicModels131 := CFSG.RankThree.PartTwo.KFacts.KS14.sporadicModels131
  have h_Step142PGLKer := step142PGLKer_of_res3 KFacts.kpSz
  have h_Step142LThreePi := CFSG.RankThree.PartTwo.Sec14.step142LThreePi_of_res (h131 := h_Item131)
    (hspor := h_SporadicModels131) (hKer := h_Step142PGLKer)
  have h_Concl142NHJS14 := CFSG.RankThree.PartTwo.Sec14.concl142NHJS14_of_item131
    (h131 := h_Item131) (h134 := h_Item134) (h48 := h_Item4_8) (h422 := h_Item4_22)
    (h45 := h_Item4_5) (hL3 := h_Step142LThreePi)
  have h_Concl143S14 := CFSG.RankThree.PartTwo.Sec14.Ronan148M.concl143S14_holds
  have h_Item143NNHJ := CFSG.RankThree.PartTwo.Sec14.Ronan148M.item143NNHJ_holds
  have h_Item1444S14 := CFSG.RankThree.PartTwo.Sec14.Ronan149.item1444S14_holds
  have h_Item148R := CFSG.RankThree.PartTwo.Sec14.Ronan148M.item148R_holds
  have h_Claim1411NonsolvWR := CFSG.RankThree.PartTwo.Sec14.claim1411NonsolvWR_holds
  have h_Claim1411NonsolvXR := CFSG.RankThree.PartTwo.Sec14.claim1411NonsolvXR_holds
  have h_Item149S14 := CFSG.RankThree.PartTwo.Sec14.Ronan149.item149S14_holds
  have h_Item4_15 := CFSG.RankThree.PartTwo.Sec4.Sporadic.rank3II_4_15
  have h_KPSz := CFSG.RankThree.PartTwo.KFacts.kpSz
  have h_Step152CompR := CFSG.RankThree.PartTwo.Sec15.step152CompR_of_item148R
    (h149 := h_Item149S14) (h148 := h_Item148R) (h134 := h_Item134) (h48 := h_Item4_8)
    (h415 := h_Item4_15) (hSz := h_KPSz)
  have h_Item148S14 := CFSG.RankThree.PartTwo.Sec14.Ronan148M.item148S14_of_frontier
  have h_Item148HJS14 := CFSG.RankThree.PartTwo.Sec14.item148HJS14_of_wired (h := h_Item148S14)
  have h_Step152ExclSL2R := CFSG.RankThree.PartTwo.Sec15.step152ExclSL2_of_item148HJ
    (h134 := h_Item134) (h48 := h_Item4_8) (h148 := h_Item148HJS14)
  have h_Step152ExclR := CFSG.RankThree.PartTwo.Sec15.step152ExclR_of (hSL2 := h_Step152ExclSL2R)
  have h_Item142AllS14 := CFSG.RankThree.PartTwo.item142AllS14_holds
  have h_Item142R := CFSG.RankThree.PartTwo.Sec14.item142R_of_wired (h := h_Item142AllS14)
  have h_Item146S14 := CFSG.RankThree.PartTwo.Sec15.Proof148FourK.item146S14_holds
  have h_Item145BotS14 := CFSG.RankThree.PartTwo.Sec14.Ronan149.item145BotS14_holds
  have h_Step152ConfTPermR := CFSG.RankThree.PartTwo.Sec15.step152ConfTPermR_of
    (h1444 := h_Item1444S14) (h146 := h_Item146S14) (hbot := h_Item145BotS14)
  have h_Item1411_1R := CFSG.RankThree.PartTwo.Sec14.item1411_1R_holds
  have h_StellmacherSzAll := CFSG.RankThree.S4Free.Stell34.stellmacherSzAll_proved.{0, 0}
  have h_StellmacherKP := (⟨h_StellmacherSzAll, h_KPSz⟩ : CFSG.RankThree.PartTwo.StellmacherKP)
  have h_Item4_25Fix := CFSG.RankThree.PartTwo.Sec4.Ronan148S.item4_25Fix_holds
  have h_Item4_1LargePrime := CFSG.RankThree.PartTwo.Sec4.diag_item41LargePrime_holds
  have h_GWLBalanceStatement := CFSG.RankThree.PartTwo.Sec6.gwlBalanceStatement_holds
  have h_Step143HJCompOne :=
    CFSG.RankThree.PartTwo.Sec14.Ronan148D.step143HJCompOne_of_item4_25Fix' (h425 := h_Item4_25Fix)
    (h134 := h_Item134) (h48 := h_Item4_8) (h41 := h_Item4_1LargePrime)
    (hGW := h_GWLBalanceStatement)
  have h_Step1515HJListLe := CFSG.RankThree.PartTwo.Sec15.step1515HJListLe_of (h148 := h_Item148R)
    (hbot := h_Item145BotS14) (h134 := h_Item134) (h48 := h_Item4_8)
  have h_Item135 := CFSG.RankThree.PartTwo.item135_holds
  have h_Item4_4 := CFSG.RankThree.PartTwo.Sec4.Census.rank3II_4_4_of_griess_noItem41
  have h_Item152BigR := CFSG.RankThree.PartTwo.Sec15.Ronan152Six.item152BigR_of (h44 := h_Item4_4)
    (hcomp := h_Step152CompR) (hexcl := h_Step152ExclR)
  have h_Item143QS14 := CFSG.RankThree.PartTwo.Sec14.Ronan148M.item143QS14_holds
  have h_Item4_1ThreeCover := CFSG.RankThree.PartTwo.Sec11.Close.closed_sec4Item4_1ThreeCover
  have h_Item4_3 := CFSG.RankThree.PartTwo.Sec4.diag_item43_holds
  have h_CoverSLThree46 := CFSG.RankThree.PartTwo.Sec4.Census.coverSLThree46
  have h_CoverCenterThree := CFSG.RankThree.PartTwo.Sec4.diag_coverCenterThree_holds
  have h_NineCoverU43RankFour := CFSG.RankThree.PartTwo.Sec4.Census.nineCoverU43RankFour
  have h_CoverInputs46 := CFSG.RankThree.PartTwo.Sec4.Census.CoverInputs46.of_open
    (hsl := h_CoverSLThree46) (hcen := h_CoverCenterThree) (hu43r := h_NineCoverU43RankFour)
  have h_Item132 := CFSG.RankThree.PartTwo.Sec13.rank3II_13_2_of (h131 := h_Item131)
    (h422 := h_Item4_22) (h45 := h_Item4_5)
  have h_Concl142S14 := CFSG.RankThree.PartTwo.Sec14.Ronan148M.concl142S14_holds
  have h_Item137 := CFSG.RankThree.PartTwo.Sec13.Ronan137H.item137_holds
  have h_KS1515M12Cover := CFSG.RankThree.PartTwo.KFacts.ks1515M12Cover
  have h_Claim1515M12 := CFSG.RankThree.PartTwo.Sec15.claim1515M12_of (hK := h_KS1515M12Cover)
    (h131 := h_Item131)
  have h_Item131a := CFSG.RankThree.PartTwo.Sec13.rank3II_13_1a_narrow
  have h_Item133 := CFSG.RankThree.PartTwo.Sec13.rank3II_13_3_of (h131 := h_Item131)
    (h422 := h_Item4_22) (h45 := h_Item4_5)
  have h_Item13SetupAt := CFSG.RankThree.PartTwo.Sec13.item13SetupAt_of (h422 := h_Item4_22)
    (h45 := h_Item4_5)
  have h_Item158Y0R := CFSG.RankThree.PartTwo.Sec15.LiebeckClosed.item158Y0R_holds
  have h_Item153BigR := CFSG.RankThree.PartTwo.Sec15.Ronan153Big.item153BigR_of_closed
    (h135 := h_Item135) (h316 := h_Item316) (h152 := h_Item152BigR)
  have h_Item146R := CFSG.RankThree.PartTwo.Sec14.item146R_of_S14 (h := h_Item146S14)
  have h_Item138N := CFSG.RankThree.PartTwo.Sec13.Ronan138S.item138_of_frontier
  have h_KS1517SeitzU := CFSG.RankThree.PartTwo.Sec14.ks1517SeitzU
  have h_KS1517CentGen := CFSG.RankThree.PartTwo.Sec15.ks1517CentGen_of (hU := h_KS1517SeitzU)
  have h_KS1517Gen := CFSG.RankThree.PartTwo.Sec15.ks1517Gen_of (h := h_KS1517CentGen)
  have h_Step159Y0Gen := CFSG.RankThree.PartTwo.Sec15.step159Y0Gen_of (h138 := h_Item138N)
    (hgen := h_KS1517Gen)
  have h_Y4CoreReadR := CFSG.RankThree.PartTwo.Sec15.Read148Perf.y4CoreReadR_from_item148R
    (hSz := h_KPSz) (hbot := h_Item145BotS14) (h148 := h_Item148R)
  have h_Y4CoreMemSolvR := CFSG.RankThree.PartTwo.Sec15.LiebeckClosed.y4CoreMemSolvR_holds
  have h_Item1411_3R := CFSG.RankThree.PartTwo.item1411_3R_holds
  have h_Step159Y0NotTrans := CFSG.RankThree.PartTwo.Sec15.step159Y0NotTrans_of'
    (h135 := h_Item135) (h138 := h_Item138N) (h142 := h_Item142R)
  have h_Step159Y0Odd := CFSG.RankThree.PartTwo.Sec15.Ronan154Big.step159Y0Odd_of_nhj
    (hRead := h_Y4CoreReadR) (h149 := h_Item149S14) (hS := h_Y4CoreMemSolvR) (h134 := h_Item134)
    (h48 := h_Item4_8) (h146 := h_Item146S14) (h1411 := h_Item1411_3R) (hNT := h_Step159Y0NotTrans)
  have h_Step159Y0 := CFSG.RankThree.PartTwo.Sec15.step159Y0_of (h135 := h_Item135)
    (h142 := h_Item142R) (hgen := h_Step159Y0Gen) (hodd := h_Step159Y0Odd)
  have h_Step159WT := CFSG.RankThree.PartTwo.Sec15.step159WT_of (h142 := h_Item142R)
  have h_Step159FiveR := CFSG.RankThree.PartTwo.Sec15.LiebeckClosed.step159FiveR_holds
  have h_Step159ClaimKY0 := CFSG.RankThree.PartTwo.Sec15.step159ClaimKY0_of (h134 := h_Item134)
    (h48 := h_Item4_8) (h148 := h_Item148R) (h5 := h_Step159FiveR)
  have h_Step159ClaimK := CFSG.RankThree.PartTwo.Sec15.Ronan154Big.step159ClaimK_of_nhj
    (hRead := h_Y4CoreReadR) (h149 := h_Item149S14) (hS := h_Y4CoreMemSolvR) (h134 := h_Item134)
    (h48 := h_Item4_8) (hbot := h_Item145BotS14) (hK := h_Step159ClaimKY0)
  have h_Step148Core := CFSG.RankThree.PartTwo.Sec14.Ronan148C.step148Core_holds
  have h_Step148Point := CFSG.RankThree.PartTwo.Sec14.Ronan148M.step148Point_holds
  have h_Step148KType := CFSG.RankThree.PartTwo.Sec14.Ronan148M.step148KType_holds
  have h_Y4BigNHJR := CFSG.RankThree.PartTwo.Sec15.Ronan154Big.y4BigNHJR_of (h134 := h_Item134)
    (h48 := h_Item4_8) (hCore := h_Step148Core) (hPoint := h_Step148Point) (hKT := h_Step148KType)
  have h_Item159R := CFSG.RankThree.PartTwo.Sec15.Ronan154Big.item159R_of_res2_big
    (h131 := h_Item131) (h133 := h_Item133) (h149 := h_Item149S14) (h153 := h_Item153BigR)
    (h1411 := h_Item1411_1R) (h146 := h_Item146R) (hY0 := h_Step159Y0) (hW := h_Step159WT)
    (hclaim := h_Step159ClaimK) (hbig := h_Y4BigNHJR)
  have h_Item1510R := CFSG.RankThree.PartTwo.Sec15.item1510R_holds
  have h_Step169TwoBridge := CFSG.RankThree.PartTwo.step169TwoBridge_holds
  have h_Item1511R := CFSG.RankThree.PartTwo.Sec15.item1511R_of_items (h142 := h_Item142R)
    (h148 := h_Item148R) (h131a := h_Item131a) (h133 := h_Item133) (h134 := h_Item134)
    (h48 := h_Item4_8) (hset := h_Item13SetupAt) (h158 := h_Item158Y0R) (h159 := h_Item159R)
    (h1510 := h_Item1510R) (hBr := h_Step169TwoBridge)
  have h_Item1511StarR := CFSG.RankThree.PartTwo.Sec15.item1511StarR_of_item1511R (h := h_Item1511R)
  have h_Step1513MeetsPoint := CFSG.RankThree.PartTwo.Sec16.step1513MeetsPoint_of_steps148
    (hCore := h_Step148Core) (hPoint := h_Step148Point) (hKT := h_Step148KType)
  have h_Step155HostE0WR := CFSG.RankThree.PartTwo.Sec15.step155HostE0WR_of_t52_switch
    h_Item4_1LargePrime h_Item4_1ThreeCover h_Item4_3 h_CoverInputs46 h_Item131 h_Item132 h_Item134
    h_Item4_8 h_Concl142S14 h_Item1444S14 h_Item137 h_Claim1515M12 h_Item1511StarR
    h_Step1513MeetsPoint h_RouteHostJ2Small h_RouteHostGood
  have h_Step155FrattiniNWPR := CFSG.RankThree.PartTwo.Sec15.step155FrattiniNWPR_of_hostE0R
    (hst := h_StellmacherKP) (h134 := h_Item134) (h48 := h_Item4_8) (h143 := h_Item143QS14)
    (h146 := h_Item146S14) (h148 := h_Item148R) (h149 := h_Item149S14) (hE0 := h_Step155HostE0WR)
  have h_Item155wJ2R := CFSG.RankThree.PartTwo.Sec15.Ronan154Big.item155wJ2R_of_big154
    (h135 := h_Item135) (h316 := h_Item316) (h152 := h_Item152BigR) (hst := h_StellmacherKP)
    (hfr := h_Step155FrattiniNWPR)
  have h_KJFix := CFSG.RankThree.PartTwo.J2Residue.kJFix_holds
  have h_KJSplit := CFSG.RankThree.PartTwo.J2Residue.kJSplit_holds
  have h_KJCover := CFSG.RankThree.PartTwo.J2Residue.kJCover_holds
  have h_Step152SL25OneOmegaResR := CFSG.RankThree.PartTwo.Sec15.step152SL25OneOmegaResR_of_j2
    (hfix := h_KJFix) (hsplit := h_KJSplit) (hcover := h_KJCover) (h142 := h_Item142AllS14)
    (h134 := h_Item134) (h48 := h_Item4_8) (hcomp := h_Step143HJCompOne)
  have h_Step152SL25OneOmegaR := CFSG.RankThree.PartTwo.Sec15.step152SL25OneOmegaR_of_res
    (h142 := h_Item142AllS14) (h134 := h_Item134) (h48 := h_Item4_8) (hcomp := h_Step143HJCompOne)
    (hlist := h_Step1515HJListLe) (h155 := h_Item155wJ2R) (hres := h_Step152SL25OneOmegaResR)
  have h_Claim1411LocalR := CFSG.RankThree.PartTwo.Sec14.claim1411LocalR_holds
  have h_KFactM2 := CFSG.RankThree.PartTwo.Sec15.ThmC.kFactM2_of_certificates
  have h_L3FieldFusionK := CFSG.RankThree.PartTwo.Sec15.F153L3K.l3FieldFusionK_holds
  have h_Step148FourKFact := CFSG.RankThree.PartTwo.Sec15.Proof148FourK.step148FourKFact_holds
  have h_Item153MainJ2R := CFSG.RankThree.PartTwo.Sec15.Ronan152Six.item153MainJ2R_of
    (hM2 := h_KFactM2) (h148 := h_Item148R) (h149 := h_Item149S14) (h142 := h_Concl142S14)
    (h143 := h_Concl143S14) (h146 := h_Item146S14) (h1444 := h_Item1444S14)
    (hbot := h_Item145BotS14) (hL3 := h_L3FieldFusionK) (hP4 := h_Step148FourKFact)
    (h152 := h_Item152BigR)
  have h_Y4CoreExclSL25HJR := CFSG.RankThree.PartTwo.Sec15.y4CoreExclSL25HJR_of_oneOmega_big
    (h1 := h_Step152SL25OneOmegaR) (h142 := h_Item142AllS14) (h425 := h_Item4_25Fix)
    (h134 := h_Item134) (h48 := h_Item4_8) (h41 := h_Item4_1LargePrime)
    (hGW := h_GWLBalanceStatement) (h148 := h_Item148R) (hbot := h_Item145BotS14)
    (hloc := h_Claim1411LocalR) (h152 := h_Item152BigR) (h153 := h_Item153MainJ2R)
    (h155 := h_Item155wJ2R)
  have h_Step152ConfKNR := CFSG.RankThree.PartTwo.Sec15.step152ConfKNR_of_excl (h134 := h_Item134)
    (h48 := h_Item4_8) (h148 := h_Item148R) (hSL25 := h_Y4CoreExclSL25HJR)
  have h_Step152ConfKXR := CFSG.RankThree.PartTwo.Sec15.step152ConfKXR_of_KN (h := h_Step152ConfKNR)
  have h_KS18Mult := CFSG.RankThree.PartTwo.KFacts.KS14.ks18Mult
  have h_Step152ConfWdR := CFSG.RankThree.PartTwo.Sec15.step152ConfWdR_of_excl (h134 := h_Item134)
    (h48 := h_Item4_8) (h148 := h_Item148R) (hSL25 := h_Y4CoreExclSL25HJR)
  have h_Step152GenTheta := CFSG.RankThree.PartTwo.Sec15.step152GenTheta_holds
  have h_KS152J2InvolNine := CFSG.RankThree.PartTwo.Sec15.ks152J2InvolNine_holds
  have h_Step152GenS := CFSG.RankThree.PartTwo.Sec15.step152GenS_of (hK := h_KS152J2InvolNine)
  have h_Step152GenX := CFSG.RankThree.PartTwo.Sec15.step152GenX_of_item142
    (h142 := h_Item142AllS14)
  have h_KS152J2Gen := CFSG.RankThree.PartTwo.Sec15.ks152J2Gen_holds
  have h_KS152HJAct := CFSG.RankThree.PartTwo.Sec15.ks152HJAct_holds
  have h_Step152ConfThetaLeDR := CFSG.RankThree.PartTwo.Sec15.step152ConfThetaLeDR_of_KX
    (h148 := h_Item148R) (h1411 := h_Item1411_1R) (h134 := h_Item134) (h48 := h_Item4_8)
    (h415 := h_Item4_15) (hst := h_StellmacherKP) (h142 := h_Item142AllS14)
    (h1444 := h_Item1444S14) (h146 := h_Item146S14) (hbot := h_Item145BotS14)
    (hKX := h_Step152ConfKXR) (h135 := h_Item135) (hmult := h_KS18Mult) (hWd := h_Step152ConfWdR)
    (hθ := h_Step152GenTheta) (hS := h_Step152GenS) (hX := h_Step152GenX) (hJ2 := h_KS152J2Gen)
    (hAct := h_KS152HJAct)
  have h_Step152ConfThetaLeR := CFSG.RankThree.PartTwo.Sec15.step152ConfThetaLeR_of_D
    (h1444 := h_Item1444S14) (h146 := h_Item146S14) (hbot := h_Item145BotS14)
    (hD := h_Step152ConfThetaLeDR)
  have h_Step152ConfThetaNormDR := CFSG.RankThree.PartTwo.Sec15.step152ConfThetaNormDR_of_KX
    (h148 := h_Item148R) (h1411 := h_Item1411_1R) (h134 := h_Item134) (h48 := h_Item4_8)
    (h415 := h_Item4_15) (hst := h_StellmacherKP) (h142 := h_Item142AllS14)
    (h1444 := h_Item1444S14) (h146 := h_Item146S14) (hbot := h_Item145BotS14)
    (hKX := h_Step152ConfKXR) (h135 := h_Item135) (hmult := h_KS18Mult) (hWd := h_Step152ConfWdR)
    (hθ := h_Step152GenTheta) (hS := h_Step152GenS) (hX := h_Step152GenX) (hJ2 := h_KS152J2Gen)
    (hAct := h_KS152HJAct)
  have h_Step152ConfThetaNormR := CFSG.RankThree.PartTwo.Sec15.step152ConfThetaNormR_of_D
    (h1444 := h_Item1444S14) (h146 := h_Item146S14) (hbot := h_Item145BotS14)
    (hD := h_Step152ConfThetaNormDR)
  have h_Step152ConfPSProdR := CFSG.RankThree.PartTwo.Sec15.step152ConfPSProdR_of
    (h1444 := h_Item1444S14) (h146 := h_Item146S14) (hbot := h_Item145BotS14)
  have h_Step152ConfPSFaithR := CFSG.RankThree.PartTwo.Sec15.step152ConfPSFaithR_of
    (h1444 := h_Item1444S14) (h146 := h_Item146S14) (hbot := h_Item145BotS14)
  have h_Step152ConfPSR := CFSG.RankThree.PartTwo.Sec15.step152ConfPSR_of
    (hprod := h_Step152ConfPSProdR) (hfaith := h_Step152ConfPSFaithR)
  have h_Step152ConfFR := CFSG.RankThree.PartTwo.Sec15.step152ConfFR_of_item142
    (h142 := h_Item142AllS14) (h135 := h_Item135) (hmult := h_KS18Mult)
  have h_Step152ConfWR := CFSG.RankThree.PartTwo.Sec15.step152ConfWR_of_Wd (h134 := h_Item134)
    (h48 := h_Item4_8) (h415 := h_Item4_15) (h142 := h_Item142AllS14) (h135 := h_Item135)
    (hmult := h_KS18Mult) (hWd := h_Step152ConfWdR)
  have h_Step152ConfR := CFSG.RankThree.PartTwo.Sec15.step152ConfR_of_confA (h142 := h_Item142R)
    (hperm := h_Step152ConfTPermR) (hle := h_Step152ConfThetaLeR)
    (hnorm := h_Step152ConfThetaNormR) (hPS := h_Step152ConfPSR) (hF := h_Step152ConfFR)
    (hW := h_Step152ConfWR)
  have h_KS152HJGen := CFSG.RankThree.PartTwo.Sec15.ks152HJGen_holds_of_item142
    (hK := h_KS152J2InvolNine) (h142 := h_Item142AllS14)
  have h_Step152EndCoverR := CFSG.RankThree.PartTwo.Sec15.step152EndCoverR_of (hX := h_Step152GenX)
  have h_Step152ConfXR := CFSG.RankThree.PartTwo.Sec15.step152ConfXR_of_res
    (h142 := h_Item142AllS14) (h1444 := h_Item1444S14) (h146 := h_Item146S14)
    (hbot := h_Item145BotS14) (h134 := h_Item134) (h135 := h_Item135) (h48 := h_Item4_8)
    (h415 := h_Item4_15) (hmult := h_KS18Mult) (hKX := h_Step152ConfKXR) (hWd := h_Step152ConfWdR)
  have h_Step152EndR := CFSG.RankThree.PartTwo.Sec15.step152EndR_of_confX (h148 := h_Item148R)
    (h1411 := h_Item1411_1R) (h134 := h_Item134) (h48 := h_Item4_8) (h415 := h_Item4_15)
    (hst := h_StellmacherKP) (hgen := h_KS152HJGen) (hAct := h_KS152HJAct)
    (hCover := h_Step152EndCoverR) (hX := h_Step152ConfXR)
  have h_Item1511S17 := CFSG.RankThree.PartTwo.Sec15.item1511S17_of_wired (h := h_Item1511R)
  have h_Item4_14_local := CFSG.RankThree.PartTwo.Sec4.Sporadic.rank3II_4_14_local
  have h_Item152R := CFSG.RankThree.PartTwo.Sec15.item152R_of (h44 := h_Item4_4)
    (h148 := h_Item148R) (h1411 := h_Item1411_1R) (h134 := h_Item134) (h48 := h_Item4_8)
    (h415 := h_Item4_15) (hst := h_StellmacherKP) (hcomp := h_Step152CompR)
    (hexcl := h_Step152ExclR) (hconf := h_Step152ConfR) (hgen := h_KS152HJGen)
    (hend := h_Step152EndR)
  have h_Claim153TwinR := CFSG.RankThree.PartTwo.Sec15.claim153TwinR_of_items (h148 := h_Item148R)
    (h149 := h_Item149S14) (h152 := h_Item152R)
  have h_KFactL3NoOuterOffender := CFSG.RankThree.PartTwo.Sec15.F153L3K.kFactL3NoOuterOffender_holds
  have h_KFactL3CentOdd := CFSG.RankThree.PartTwo.Sec15.F153L3K.kFactL3CentOdd_holds
  have h_Step153PushL3Char2R := CFSG.RankThree.PartTwo.Sec15.F153L3C2.step153PushL3Char2R_of_inputs
    (h134 := h_Item134) (h48 := h_Item4_8) (h149 := h_Item149S14) (htwin := h_Claim153TwinR)
    (h148 := h_Item148HJS14) (hOut := h_KFactL3NoOuterOffender) (hCent := h_KFactL3CentOdd)
  have h_Claim153CharR := CFSG.RankThree.PartTwo.Sec15.F153.claim153CharR_of_frontier_obs3
    (h316 := h_Item316) (h149 := h_Item149S14) (h148 := h_Item148R) (h152 := h_Item152R)
    (h134 := h_Item134) (h135 := h_Item135) (h137 := h_Item137) (h142 := h_Item142AllS14)
    (h48 := h_Item4_8) (h415 := h_Item4_15) (hM2 := h_KFactM2) (h142c := h_Concl142S14)
    (h143 := h_Concl143S14) (h146 := h_Item146S14) (h1444 := h_Item1444S14)
    (hbot := h_Item145BotS14) (hL3 := h_L3FieldFusionK) (hP4 := h_Step148FourKFact)
    (hL3two := h_Step153PushL3Char2R)
  have h_Item153MainR := CFSG.RankThree.PartTwo.Sec15.item153MainR_of_twin (h149 := h_Item149S14)
    (htwin := h_Claim153TwinR) (hchar := h_Claim153CharR)
  have h_Claim153TwinCase7 := CFSG.RankThree.PartTwo.Sec15.claim153TwinCase7_of_item148R
    (h148 := h_Item148R)
  have h_Claim153TwinTypes := CFSG.RankThree.PartTwo.Sec15.claim153TwinTypes_of
    (h148 := h_Item148R) (h149 := h_Item149S14) (h152 := h_Item152R) (h7 := h_Claim153TwinCase7)
  have h_Claim156QR := CFSG.RankThree.PartTwo.Sec15.claim156QR_of_item153MainR
    (h153 := h_Item153MainR)
  have h_KL3a := CFSG.RankThree.PartTwo.Sec15.Wales154.kl3a_holds
  have h_KL3c := CFSG.RankThree.PartTwo.Sec15.Wales154.kl3c_holds
  have h_Item154L3Five := CFSG.RankThree.PartTwo.Sec15.Wales154.item154L3Five_of_items
    (h158 := h_Item158Y0R) (hset := h_Item13SetupAt) (h133 := h_Item133) (h159 := h_Item159R)
    (h1510 := h_Item1510R) (hBr := h_Step169TwoBridge) (h134 := h_Item134) (h48 := h_Item4_8)
  have h_Item154ProperR := CFSG.RankThree.PartTwo.Sec15.Wales154.item154ProperR_of_five
    (h148 := h_Item148R) (h134 := h_Item134) (h48 := h_Item4_8) (hbot := h_Item145BotS14)
    (h142 := h_Item142R) (hKa := h_KL3a) (hKc := h_KL3c) (h5 := h_Item154L3Five)
  have h_Item154R := CFSG.RankThree.PartTwo.Sec15.item154R_of_proper (h := h_Item154ProperR)
  have h_Y4LThreePiNHJR := CFSG.RankThree.PartTwo.Sec15.Ronan155Y.y4LThreePiNHJR_holds
  have h_Step155GrowAltWR := CFSG.RankThree.PartTwo.Sec15.Ronan155Y.step155GrowAltWR_holds
  have h_Step155GrowWR := CFSG.RankThree.PartTwo.Sec15.step155GrowWR_of (h1444 := h_Item1444S14)
    (h146 := h_Item146S14) (hbot := h_Item145BotS14) (h154 := h_Item154R)
    (halt := h_Step155GrowAltWR)
  have h_Step155YQ0HypWR := CFSG.RankThree.PartTwo.Sec15.Proof148FourK.step155YQ0HypWR_holds
  have h_Step155PJQ0HypWR := CFSG.RankThree.PartTwo.Sec15.Proof148FourK.step155PJQ0HypWR_holds
  have h_Step155CasesTwoNHJWR :=
    CFSG.RankThree.PartTwo.Sec15.Ronan155R.step155CasesTwoNHJWR_of_route' (hY4 := h_Y4LThreePiNHJR)
    (h152 := h_Item152R) (h153 := h_Item153MainR) (hgrow := h_Step155GrowWR) (h146 := h_Item146S14)
    (h1444 := h_Item1444S14) (hbot := h_Item145BotS14) (h142 := h_Concl142S14)
    (hYQ := h_Step155YQ0HypWR) (hPJQ := h_Step155PJQ0HypWR)
  have h_Item155wR := CFSG.RankThree.PartTwo.Sec15.Closed155W9.item155wR_of_frontier
    (hSL25 := h_Y4CoreExclSL25HJR) (h135 := h_Item135) (h316 := h_Item316) (h154 := h_Item154R)
    (htwo := h_Step155CasesTwoNHJWR) (hst := h_StellmacherKP) (hfr := h_Step155FrattiniNWPR)
  have h_Step156CQA5DFaithR :=
    CFSG.RankThree.PartTwo.Sec15.Liebeck156.step156CQA5DFaithR_of_item153 (h153 := h_Item153MainR)
  have h_Step156CQA5DR := CFSG.RankThree.PartTwo.Sec15.step156CQA5DR_of_faith
    (h142 := h_Item142AllS14) (h152 := h_Item152R) (h153 := h_Item153MainR) (hw := h_Item155wR)
    (hrest := h_Step156CQA5DFaithR)
  have h_Step156CQA5R := CFSG.RankThree.PartTwo.Sec15.step156CQA5R_of (h134 := h_Item134)
    (h48 := h_Item4_8) (h142 := h_Item142AllS14) (h152 := h_Item152R) (hD := h_Step156CQA5DR)
  have h_Step156CQOmegaR := CFSG.RankThree.PartTwo.Sec15.step156CQOmegaR_of (h134 := h_Item134)
    (h48 := h_Item4_8)
  have h_Step156QThetaMeetR := CFSG.RankThree.PartTwo.Sec15.step156QThetaMeetR_of
    (h142 := h_Item142AllS14) (h152 := h_Item152R) (h153 := h_Item153MainR) (hw := h_Item155wR)
  have h_Step156CQFaithfulNR := CFSG.RankThree.PartTwo.Sec15.step156CQFaithfulNR_of_meet
    (h134 := h_Item134) (h48 := h_Item4_8) (h142 := h_Item142AllS14) (hMF := h_Step156QThetaMeetR)
  have h_Step156CQFaithfulR := CFSG.RankThree.PartTwo.Sec15.step156CQFaithfulR_of
    (h142 := h_Item142AllS14) (hN := h_Step156CQFaithfulNR)
  have h_Claim153NoTwinA5A6 := CFSG.RankThree.PartTwo.Sec15.claim153NoTwinA5A6_of_small
    (h148 := h_Item148R) (h152 := h_Item152R) (hq := h_Claim156QR) (h1411 := h_Item1411_1R)
    (h134 := h_Item134) (h48 := h_Item4_8) (h142 := h_Item142AllS14) (hA5 := h_Step156CQA5R)
    (hΩ := h_Step156CQOmegaR) (hP := h_Step156CQFaithfulR)
  have h_Claim153NormalNoE9R := CFSG.RankThree.PartTwo.Sec15.claim153NormalNoE9R_of
    (htypes := h_Claim153TwinTypes) (hno := h_Claim153NoTwinA5A6)
  have h_Claim153NormalR := CFSG.RankThree.PartTwo.Sec15.claim153NormalR_of_wired
    (h152 := h_Item152R) (hno := h_Claim153NormalNoE9R)
  have h_KS1513Z3PGLOrderThree := CFSG.RankThree.PartTwo.Sec15.ks1513Z3PGLOrderThree
  have h_Y4CoreMemR := CFSG.RankThree.PartTwo.Sec15.y4CoreMemR_of_excl (h149 := h_Item149S14)
    (hS := h_Y4CoreMemSolvR) (h134 := h_Item134) (h48 := h_Item4_8) (h148 := h_Item148R)
    (hSL25 := h_Y4CoreExclSL25HJR)
  have h_Step1513MaxJ := CFSG.RankThree.PartTwo.Sec15.step1513MaxJ_of_core (hRead := h_Y4CoreReadR)
    (hMem := h_Y4CoreMemR) (hbot := h_Item145BotS14)
  have h_Step1513EvenNotM12 := CFSG.RankThree.PartTwo.Sec15.step1513EvenNotM12_of
    (h131 := h_Item131)
  have h_Step1513EvenType := CFSG.RankThree.PartTwo.Sec15.step1513EvenType_of (h131 := h_Item131)
    (h142 := h_Concl142S14) (hM12 := h_Step1513EvenNotM12)
  have h_Step1513EvenTrans := CFSG.RankThree.PartTwo.Sec15.step1513EvenTrans_of_named
    (h142 := h_Item142R) (hbot := h_Item145BotS14)
  have h_Item1513R := CFSG.RankThree.PartTwo.Sec15.item1513R_of_steps (h131 := h_Item131)
    (h132 := h_Item132) (h133 := h_Item133) (h134 := h_Item134) (h137 := h_Item137)
    (h48 := h_Item4_8) (h414 := h_Item4_14_local) (h415 := h_Item4_15) (hset := h_Item13SetupAt)
    (h146 := h_Item146S14) (h159 := h_Item159R) (h1510 := h_Item1510R) (hBr := h_Step169TwoBridge)
    (h1511 := h_Item1511R) (h1411 := h_Item1411_1R) (hloc := h_Claim1411LocalR)
    (h153 := h_Item153MainR) (hnorm := h_Claim153NormalR) (hcl := h_Claim1515M12)
    (hKf := h_KS1513Z3PGLOrderThree) (hpt := h_Step1513MeetsPoint) (hJ := h_Step1513MaxJ)
    (htype := h_Step1513EvenType) (htrans := h_Step1513EvenTrans)
  have h_Item1513S17 := CFSG.RankThree.PartTwo.Sec15.item1513S17_of_wired (h := h_Item1513R)
  have h_Step1515A7Omega := CFSG.RankThree.PartTwo.Sec15.step1515A7Omega_of (h148 := h_Item148R)
    (hbot := h_Item145BotS14) (h131 := h_Item131) (h135 := h_Item135)
  have h_Step1515M22 := CFSG.RankThree.PartTwo.Sec15.step1515M22_of (h148 := h_Item148R)
    (hbot := h_Item145BotS14) (h142 := h_Item142R)
  have h_Step1515S17 := CFSG.RankThree.PartTwo.Sec15.step1515S17_of_res (h131 := h_Item131)
    (h137 := h_Item137) (h1511 := h_Item1511S17) (h1513 := h_Item1513S17)
    (hA7O := h_Step1515A7Omega) (hM22 := h_Step1515M22) (hHJL := h_Step1515HJListLe)
  have h_Step1519S17 := CFSG.RankThree.PartTwo.Sec15.step1519S17
  have h_Step1521S17 := CFSG.RankThree.PartTwo.Sec15.step1521S17
  have h_Step1522S17 := CFSG.RankThree.PartTwo.Sec15.step1522S17
  have h_SLTwoCenter := CFSG.RankThree.PartTwo.Sec13.slTwoCenter
  have h_KS15M22Gen := CFSG.RankThree.PartTwo.Sec15.ks15M22Gen_of_items (h148 := h_Item148R)
    (hbot := h_Item145BotS14) (h142 := h_Item142R) (h131 := h_Item131) (h134 := h_Item134)
    (h48 := h_Item4_8) (h135 := h_Item135)
  have h_Claim153ObsR := CFSG.RankThree.PartTwo.Sec15.claim153ObsR_of_wired (h149 := h_Item149S14)
    (hn := h_Claim153NormalR)
  have h_Item1512R := CFSG.RankThree.PartTwo.Sec15.item1512R_of_wired (h131 := h_Item131)
    (hspor := h_SporadicModels131) (hSLC := h_SLTwoCenter) (hgen := h_KS15M22Gen)
    (h159 := h_Item159R) (h1411 := h_Item1411_1R) (h153 := h_Item153MainR) (hobs := h_Claim153ObsR)
  have h_Item156R := CFSG.RankThree.PartTwo.Sec15.Closed155W9.item156R_of_frontier
    (hSL25 := h_Y4CoreExclSL25HJR) (h135 := h_Item135) (h316 := h_Item316) (h154 := h_Item154R)
    (h1411 := h_Item1411_1R) (hrest := h_Step156CQA5DFaithR) (htwo := h_Step155CasesTwoNHJWR)
    (hst := h_StellmacherKP) (hfr := h_Step155FrattiniNWPR)
  have h_Item4_4Types135 := CFSG.RankThree.PartTwo.Sec13.item4_4Types135_of_item4_4
    (h44 := h_Item4_4)
  have h_KS135TwoRankCover := CFSG.RankThree.PartTwo.Sec13.ks135TwoRankCover
  have h_KS135TwoRank := CFSG.RankThree.PartTwo.Sec13.ks135TwoRank_of_cover
    (hC := h_KS135TwoRankCover) (h414 := h_Item4_14_local) (h415 := h_Item4_15)
  have h_Item135SimpleReduce := CFSG.RankThree.PartTwo.Sec13.item135SimpleReduce_narrow
    (h44 := h_Item4_4Types135) (hK := h_KS135TwoRank) (hspor := h_SporadicModels131)
    (h414 := h_Item4_14_local) (h415 := h_Item4_15)
  have h_Item135SimpleL3 := CFSG.RankThree.PartTwo.Sec13.item135SimpleL3
  have h_Item135Simple := CFSG.RankThree.PartTwo.Sec13.item135Simple_of_steps
    (hR := h_Item135SimpleReduce) (hL3 := h_Item135SimpleL3)
  have h_Concl142R := CFSG.RankThree.PartTwo.Sec14.concl142R_of_S14 (h := h_Concl142S14)
  have h_Step143Balance := CFSG.RankThree.PartTwo.Sec14.step143Balance_holds
  have h_Step1515HJEndFpfRBoundOff :=
    CFSG.RankThree.PartTwo.Sec15.Gagen1515Fpf.step1515HJEndFpfRBoundOff_holds
    (hbal := h_Step143Balance) (h134 := h_Item134) (h48 := h_Item4_8) (h45 := h_Item4_5)
    (h143 := h_Item143QS14) (h142 := h_Item142R) (hc142 := h_Concl142R) (h146 := h_Item146S14)
    (h148 := h_Item148R) (h152 := h_Item152R) (h153 := h_Item153MainR) (h1411 := h_Item1411_1R)
  have h_KS1515ONCent := CFSG.RankThree.PartTwo.Sec15.ks1515ONCent_holds
  have h_Step1515HJEndFpfA6A6Meet :=
    CFSG.RankThree.PartTwo.Sec15.Liebeck1515B.step1515HJEndFpfA6A6Meet_of (h316 := h_Item316)
    (h152 := h_Item152R) (h153 := h_Item153MainR) (h142 := h_Concl142R)
  have h_Step1515HJEndFpfRCore := CFSG.RankThree.PartTwo.Sec15.step1515HJEndFpfRCore_of_meet
    (hbal := h_Step143Balance) (h134 := h_Item134) (h48 := h_Item4_8) (h142 := h_Concl142R)
    (h143 := h_Item143QS14) (hON := h_KS1515ONCent) (hoff := h_Step1515HJEndFpfRBoundOff)
    (hmeet := h_Step1515HJEndFpfA6A6Meet)
  have h_Step1515HJEndFpfA6A6 := CFSG.RankThree.PartTwo.Sec15.step1515HJEndFpfA6A6_of_core
    (hC := h_Step1515HJEndFpfRCore)
  have h_KL325ThetaCent := CFSG.RankThree.PartTwo.Sec15.kl325ThetaCent
  have h_KL325SubgroupOrder := CFSG.RankThree.PartTwo.Sec15.KL3Sub3Proof.kl325SubgroupOrder
  have h_Step1515R := CFSG.RankThree.PartTwo.Sec14.Ronan143Q.step1515R_of_res11Q
    (h131 := h_Item131) (h137 := h_Item137) (hcl := h_Claim1515M12) (h1511 := h_Item1511R)
    (h1512 := h_Item1512R) (h1513 := h_Item1513R) (h156 := h_Item156R) (h148 := h_Item148R)
    (hbot := h_Item145BotS14) (h142 := h_Item142R) (h134 := h_Item134) (h48 := h_Item4_8)
    (h135 := h_Item135) (h135s := h_Item135Simple) (h153 := h_Item153MainR)
    (hobs := h_Claim153ObsR) (h149 := h_Item149S14) (h1411 := h_Item1411_1R)
    (hloc := h_Claim1411LocalR) (h1444 := h_Item1444S14) (h146 := h_Item146S14)
    (hc142 := h_Concl142R) (h152 := h_Item152R) (hgen := h_KS1517Gen) (h155 := h_Item155wR)
    (h143 := h_Item143QS14) (hoff := h_Step1515HJEndFpfRBoundOff) (hON := h_KS1515ONCent)
    (hA6 := h_Step1515HJEndFpfA6A6) (hθ := h_KL325ThetaCent) (hK325 := h_KL325SubgroupOrder)
  have h_Step1516R := CFSG.RankThree.PartTwo.Sec15.step1516R_of (h153 := h_Item153MainR)
    (hobs := h_Claim153ObsR) (h149 := h_Item149S14) (h1411 := h_Item1411_1R)
    (hloc := h_Claim1411LocalR)
  have h_Step1517Q0 := CFSG.RankThree.PartTwo.Sec15.step1517Q0_of (h1444 := h_Item1444S14)
    (h146 := h_Item146S14) (hbot := h_Item145BotS14) (h142 := h_Concl142S14)
  have h_Step1517R := CFSG.RankThree.PartTwo.Sec15.step1517R_of_named (h135 := h_Item135Simple)
    (h142 := h_Concl142R) (h152 := h_Item152R) (h1510 := h_Item1510R) (hbr := h_Step169TwoBridge)
    (h138 := h_Item138N) (hgen := h_KS1517Gen) (h153 := h_Item153MainR) (hobs := h_Claim153ObsR)
    (h1411 := h_Item1411_1R) (hq0 := h_Step1517Q0)
  have h_Step1518TL := CFSG.RankThree.PartTwo.Sec15.step1518TL_of (h142 := h_Item142R)
    (h138 := h_Item138N)
  have h_KS1518Norm := CFSG.RankThree.PartTwo.Sec15.KL3Sub2Proof.ks1518Norm
  have h_Step1518R := CFSG.RankThree.PartTwo.Sec15.step1518R_of_norm (h1516 := h_Step1516R)
    (h1517 := h_Step1517R) (hTL := h_Step1518TL) (hN := h_KS1518Norm)
  have h_Step1519Y0E9 := CFSG.RankThree.PartTwo.Sec15.step1519Y0E9_of (h1511 := h_Item1511R)
    (hpt := h_Step1513MeetsPoint) (h148 := h_Item148R) (hbot := h_Item145BotS14)
    (h138 := h_Item138N)
  have h_Step1519CentAut := CFSG.RankThree.PartTwo.Sec15.step1519CentAut_of_y0E9'
    (hD := h_Step1519Y0E9)
  have h_Step1519R := CFSG.RankThree.PartTwo.Sec15.step1519R_of_named (h1518 := h_Step1518R)
    (h1517 := h_Step1517R) (h135 := h_Item135Simple) (h142 := h_Concl142R) (h1510 := h_Item1510R)
    (hbr := h_Step169TwoBridge) (h138 := h_Item138N) (hcent := h_Step1519CentAut)
  have h_Item14_23R := CFSG.RankThree.PartTwo.Sec15.item14_23R_of (h45 := h_Item4_5)
    (hSz := h_KPSz) (h142 := h_Item142R)
  have h_Step1520Comm := CFSG.RankThree.PartTwo.Sec15.step1520Comm_of_item138N
    (h1517 := h_Step1517R) (h138 := h_Item138N)
  have h_Step1520CoreComp := CFSG.RankThree.PartTwo.Sec15.step1520CoreComp_of_core
    (hRead := h_Y4CoreReadR) (hMem := h_Y4CoreMemR) (hbot := h_Item145BotS14)
  have h_Step1520Core := CFSG.RankThree.PartTwo.Sec15.step1520Core_of (hcomm := h_Step1520Comm)
    (hcomp := h_Step1520CoreComp)
  have h_Step1520R := CFSG.RankThree.PartTwo.Sec15.step1520R_of (h1423 := h_Item14_23R)
    (hcore := h_Step1520Core) (hcomm := h_Step1520Comm)
  have h_Step1521T := CFSG.RankThree.PartTwo.Sec15.step1521T_of (h1520 := h_Step1520R)
    (h1517 := h_Step1517R) (h138 := h_Item138N) (h146 := h_Item146S14) (h1444 := h_Item1444S14)
    (hst := h_StellmacherKP)
  have h_Step1521CY := CFSG.RankThree.PartTwo.Sec15.step1521CY_of_step1517R (h1517 := h_Step1517R)
  have h_Step1521UConj := CFSG.RankThree.PartTwo.Sec15.step1521UConj_of_T (h153 := h_Item153MainR)
    (hobs := h_Claim153ObsR) (h1411 := h_Item1411_1R) (h146 := h_Item146S14) (hq0 := h_Step1517Q0)
    (hT := h_Step1521T) (hcy := h_Step1521CY)
  have h_Step1521Gen := CFSG.RankThree.PartTwo.Sec15.step1521Gen_of_step1517R (h1517 := h_Step1517R)
  have h_Step1521U := CFSG.RankThree.PartTwo.Sec15.step1521U_of (hU := h_Step1521UConj)
    (hnorm := h_Claim153NormalR) (hgen := h_Step1521Gen)
  have h_Step1521R := CFSG.RankThree.PartTwo.Sec15.step1521R_of (h1520 := h_Step1520R)
    (hU := h_Step1521U) (hnorm := h_Claim153NormalR) (hgen := h_Step1521Gen)
  have h_KS1424NonToral := CFSG.RankThree.PartTwo.Sec15.ks1424NonToral
  have h_KS1424Torus := CFSG.RankThree.PartTwo.Sec15.ks1424Torus
  have h_Step1424E := CFSG.RankThree.PartTwo.Sec15.step1424E_of (h142 := h_Concl142S14)
    (hNT := h_KS1424NonToral) (hT := h_KS1424Torus)
  have h_KS1424Core := CFSG.RankThree.PartTwo.Sec15.ks1424Core
  have h_Step1424Core := CFSG.RankThree.PartTwo.Sec15.step1424Core_of (hK := h_KS1424Core)
  have h_Item14_24R := CFSG.RankThree.PartTwo.Sec14.Ronan143Q.item14_24R_ofQ
    (h1423 := h_Item14_23R) (h143 := h_Item143QS14) (hE := h_Step1424E) (hcore := h_Step1424Core)
  have h_Step1522HypMeet := CFSG.RankThree.PartTwo.Sec15.step1522HypMeet_of_item138N
    (h1517 := h_Step1517R) (h1518 := h_Step1518R) (h138 := h_Item138N)
  have h_Step1522HypNotL34 := CFSG.RankThree.PartTwo.Sec15.step1522HypNotL34_of_meet
    (hmeet := h_Step1522HypMeet)
  have h_Step1522R := CFSG.RankThree.PartTwo.Sec15.step1522R_of_kfacts (h1424 := h_Item14_24R)
    (h153 := h_Item153MainR) (h1517 := h_Step1517R) (h1518 := h_Step1518R) (h138 := h_Item138N)
    (hl34 := h_Step1522HypNotL34)
  have h_Item1514R := CFSG.RankThree.PartTwo.Sec15.item1514R_of (h1515 := h_Step1515R)
    (h1519 := h_Step1519R) (h1521 := h_Step1521R) (h1522 := h_Step1522R)
  have h_KS1515ONMult := CFSG.RankThree.PartTwo.Sec15.ks1515ONMult
  have h_Step1515HJListA7 := CFSG.RankThree.PartTwo.Sec15.step1515HJListA7_of_item142
    (h142 := h_Item142R)
  have h_Step1515HJConj := CFSG.RankThree.PartTwo.Sec15.step1515HJConj_of (h152 := h_Item152R)
    (h153 := h_Item153MainR) (h155 := h_Item155wR)
  have h_Step1515HJQN := CFSG.RankThree.PartTwo.Sec15.step1515HJQN_of (h152 := h_Item152R)
    (h153 := h_Item153MainR) (h155 := h_Item155wR)
  have h_Step1515HJVFour := CFSG.RankThree.PartTwo.Sec15.step1515HJVFour_of_res10
  have h_Step1515HJVR := CFSG.RankThree.PartTwo.Sec15.step1515HJVR_of_res10
  have h_Step1515HJVBlockM := CFSG.RankThree.PartTwo.Sec15.step1515HJVBlockM_of_res10
  have h_Step1515HJEndFpfX := CFSG.RankThree.PartTwo.Sec15.step1515HJEndFpfX_of_core
    (h152 := h_Item152R) (h153 := h_Item153MainR) (hC := h_Step1515HJEndFpfRCore)
  have h_Step1515HJEndX := CFSG.RankThree.PartTwo.Sec15.step1515HJEndX_of_res7 (h134 := h_Item134)
    (h48 := h_Item4_8) (h152 := h_Item152R) (h153 := h_Item153MainR) (h155 := h_Item155wR)
    (hF := h_Step1515HJEndFpfX)
  have h_Step1515HJEndFpfT0 := CFSG.RankThree.PartTwo.Sec15.step1515HJEndFpfT0_of_core
    (h152 := h_Item152R) (h153 := h_Item153MainR) (hC := h_Step1515HJEndFpfRCore)
  have h_Step1515HJEndT0 := CFSG.RankThree.PartTwo.Sec15.step1515HJEndT0_of_res7
    (h134 := h_Item134) (h48 := h_Item4_8) (h152 := h_Item152R) (h153 := h_Item153MainR)
    (h155 := h_Item155wR) (hF := h_Step1515HJEndFpfT0)
  have h_Step1515HJ := CFSG.RankThree.PartTwo.Sec15.step1515HJ_of_res4 (h134 := h_Item134)
    (h48 := h_Item4_8) (hloc := h_Claim1411LocalR) (h316 := h_Item316) (hC := h_Step1515HJConj)
    (hQN := h_Step1515HJQN) (hF := h_Step1515HJVFour) (hR := h_Step1515HJVR)
    (hB := h_Step1515HJVBlockM) (hX := h_Step1515HJEndX) (hT := h_Step1515HJEndT0)
  have h_Step1515HJListCover := CFSG.RankThree.PartTwo.Sec15.step1515HJListCover_of
    (h142 := h_Item142R) (h134 := h_Item134) (h48 := h_Item4_8) (h135 := h_Item135Simple)
    (hHJ := h_Step1515HJ)
  have h_Step1515HJList := CFSG.RankThree.PartTwo.Sec15.step1515HJList_of (h148 := h_Item148R)
    (hbot := h_Item145BotS14) (h142 := h_Item142R) (h134 := h_Item134) (h48 := h_Item4_8)
    (h135 := h_Item135Simple) (hON := h_KS1515ONMult) (hA7 := h_Step1515HJListA7)
    (hcov := h_Step1515HJListCover)
  have h_Item1514HJR := CFSG.RankThree.PartTwo.Sec15.item1514HJR_of (h131 := h_Item131)
    (h156 := h_Item156R) (hHJL := h_Step1515HJList) (hHJ := h_Step1515HJ)
  have h_KS1523ONCent := CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KS1523ON.ks1523ONCent_holds
  have h_Item155R := CFSG.RankThree.PartTwo.Sec15.Closed155W9.item155R_of_frontier
    (hSL25 := h_Y4CoreExclSL25HJR) (h135 := h_Item135) (h316 := h_Item316) (h154 := h_Item154R)
    (h1411 := h_Item1411_1R) (hrest := h_Step156CQA5DFaithR) (htwo := h_Step155CasesTwoNHJWR)
    (hst := h_StellmacherKP) (hfr := h_Step155FrattiniNWPR)
  have h_Item155HJR := CFSG.RankThree.PartTwo.Sec15.item155HJR_of_item155R (h := h_Item155R)
  have h_Step1523KSolv := CFSG.RankThree.PartTwo.Sec14.Ronan143Q.step1523KSolv_ofQ
    (h45 := h_Item4_5) (hSz := h_KPSz) (h143 := h_Item143QS14)
  have h_Step1523KTypeY4 := CFSG.RankThree.PartTwo.Sec14.Ronan143Q.step1523KTypeY4_of_solvQ
    (h134 := h_Item134) (h143 := h_Item143QS14) (h149 := h_Item149S14) (hsolv := h_Step1523KSolv)
  have h_Step1523KReadY4 := CFSG.RankThree.PartTwo.Sec15.step1523KReadY4_of_type
    (h148 := h_Item148R) (h134 := h_Item134) (h48 := h_Item4_8) (h142 := h_Item142R)
    (h156 := h_Item156R) (h1514 := h_Item1514HJR) (hT := h_Step1523KTypeY4)
  have h_KS1523NormTwo := CFSG.RankThree.PartTwo.Sec15.ks1523NormTwo_holds
  have h_Step1523ZPickY4 := CFSG.RankThree.PartTwo.Sec15.step1523ZPickY4_of_ks
    (hKS := h_KS1523NormTwo)
  have h_KS1523HJTwo := CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KS1523.ks1523HJTwo_holds
  have h_Item1523R := CFSG.RankThree.PartTwo.Sec15.item1523R_of_res12b (h134 := h_Item134)
    (h48 := h_Item4_8) (h142 := h_Concl142S14) (h143 := h_Concl143S14) (h152 := h_Item152R)
    (h1514 := h_Item1514HJR) (h153 := h_Item153MainR) (h149 := h_Item149S14)
    (hON := h_KS1523ONCent) (h155 := h_Item155HJR) (hKR := h_Step1523KReadY4)
    (hP := h_Step1523ZPickY4) (hKS := h_KS1523HJTwo)
  have h_Item148SmallS14 := CFSG.RankThree.PartTwo.Sec14.Ronan149.item148SmallS14_holds
  have h_Step1610 := CFSG.RankThree.PartTwo.Sec16.step1610_of_core (hRead := h_Y4CoreReadR)
    (hMem := h_Y4CoreMemR) (hbot := h_Item145BotS14)
  have h_Step1611List := CFSG.RankThree.PartTwo.Sec16.step1611List_of_item131 (h131 := h_Item131)
  have h_Step1611 := CFSG.RankThree.PartTwo.Sec16.step1611_of (h1610 := h_Step1610)
    (h146 := h_Item146S14) (hbot := h_Item145BotS14) (h1411 := h_Item1411_3R) (h142 := h_Item142R)
    (hL := h_Step1611List)
  have h_KS169HJNotTrans := CFSG.RankThree.PartTwo.Sec16.ks169HJNotTrans
  have h_KS1611A7NotTrans := CFSG.RankThree.PartTwo.Sec16.ks1611A7NotTrans
  have h_KS1611M22NotTrans := CFSG.RankThree.PartTwo.Sec16.ks1611M22NotTrans
  have h_KS1611M12NotTrans := CFSG.RankThree.PartTwo.Sec16.ks1611M12NotTrans
  have h_KS1611OddAut := CFSG.RankThree.PartTwo.Sec16.ks1611OddAut_of (h131a := h_Item131a)
  have h_KS1611OddNotTrans := CFSG.RankThree.PartTwo.Sec16.ks1611OddNotTrans_of_aut
    (hAut := h_KS1611OddAut)
  have h_Step1612Gen := CFSG.RankThree.PartTwo.Sec16.step1612Gen_of_item131 (h131 := h_Item131)
  have h_Step1612 := CFSG.RankThree.PartTwo.Sec16.step1612_of_steps169_core
    (hRead := h_Y4CoreReadR) (hMem := h_Y4CoreMemR) (h152 := h_Item152R) (h146 := h_Item146S14)
    (hbot := h_Item145BotS14) (h1411 := h_Item1411_3R) (h142 := h_Item142R) (h131 := h_Item131)
    (hHJ := h_KS169HJNotTrans) (hA7 := h_KS1611A7NotTrans) (hM22 := h_KS1611M22NotTrans)
    (hM12 := h_KS1611M12NotTrans) (hOdd := h_KS1611OddNotTrans) (h135 := h_Item135Simple)
    (h138 := h_Item138N) (hgen := h_Step1612Gen)
  have h_Item163R := CFSG.RankThree.PartTwo.Sec14.Ronan143Q.item163R_of_routes_coreQ
    (h1514 := h_Item1514R) (h1523 := h_Item1523R) (h153 := h_Item153MainR) (hobs := h_Claim153ObsR)
    (hn := h_Claim153NormalR) (h155 := h_Item155R) (hW := h_Claim1411NonsolvWR)
    (hX := h_Claim1411NonsolvXR) (h142 := h_Concl142S14) (h142All := h_Item142AllS14)
    (h143c := h_Concl143S14) (h143 := h_Item143NNHJ) (h1444 := h_Item1444S14)
    (h146 := h_Item146S14) (hbot := h_Item145BotS14) (h148 := h_Item148R)
    (h148S := h_Item148SmallS14) (hCore := h_Step148Core) (hPoint := h_Step148Point)
    (hKT := h_Step148KType) (hRead := h_Y4CoreReadR) (hMem := h_Y4CoreMemR) (h131 := h_Item131)
    (h135 := h_Item135) (h1424 := h_Item14_24R) (h1510 := h_Item1510R) (h135S := h_Item135Simple)
    (h138 := h_Item138N)
  have h_Step163MeetsPoint := CFSG.RankThree.PartTwo.Sec16.step163MeetsPoint_of_step1513MeetsPoint
    (h := h_Step1513MeetsPoint)
  have h_Step163Meets := CFSG.RankThree.PartTwo.Sec16.step163Meets_of_point (h1514 := h_Item1514R)
    (h1523 := h_Item1523R) (h153 := h_Item153MainR) (hobs := h_Claim153ObsR)
    (h1411 := h_Item1411_1R) (hM := h_Step163MeetsPoint)
  have h_Step1614 := CFSG.RankThree.PartTwo.Sec14.Ronan143Q.step1614_of_res12Q
    (h1611 := h_Step1611) (h1612 := h_Step1612) (h131 := h_Item131) (h133 := h_Item133)
    (h138 := h_Item138N) (h143 := h_Item143QS14) (h1510 := h_Item1510R) (hBr := h_Step169TwoBridge)
    (hset := h_Item13SetupAt) (h41 := h_Item4_1LargePrime) (h163 := h_Item163R)
    (hMeets := h_Step163Meets) (h1514 := h_Item1514R) (h1411 := h_Item1411_1R)
  have h_Step1615 := CFSG.RankThree.PartTwo.Sec14.Ronan143Q.step1615_of_res12Q
    (h1611 := h_Step1611) (h1612 := h_Step1612) (h131 := h_Item131) (h133 := h_Item133)
    (h138 := h_Item138N) (h143 := h_Item143QS14) (h1510 := h_Item1510R) (hBr := h_Step169TwoBridge)
    (hset := h_Item13SetupAt) (h41 := h_Item4_1LargePrime) (h163 := h_Item163R)
    (hMeets := h_Step163Meets) (h1514 := h_Item1514R)
  have h_KS1615Meet := CFSG.RankThree.PartTwo.Sec16.ks1615Meet
  have h_Step1616Fix := CFSG.RankThree.PartTwo.Sec16.step1616Fix_of_steps (h1612 := h_Step1612)
    (h131 := h_Item131) (h138 := h_Item138N)
  have h_Step1616Comm := CFSG.RankThree.PartTwo.Sec16.step1616Comm_of (h1411 := h_Item1411_1R)
  have h_KSL3PiNoSz := CFSG.RankThree.PartTwo.Sec16.kSL3PiNoSz_holds
  have h_Step1616OmegaSolv := CFSG.RankThree.PartTwo.Sec16.step1616OmegaSolv_of
    (h1612 := h_Step1612) (hNoSz := h_KSL3PiNoSz)
  have h_KS1616SzOdd := CFSG.RankThree.PartTwo.Sec16.Res3Omega.ks1616SzOdd
  have h_Step1616OmegaSz := CFSG.RankThree.PartTwo.Sec16.step1616OmegaSz_of_solv
    (hSolv := h_Step1616OmegaSolv) (hK := h_KS1616SzOdd)
  have h_Step1616Omega := CFSG.RankThree.PartTwo.Sec14.Ronan143Q.step1616Omega_ofQ
    (h1611 := h_Step1611) (h143 := h_Item143QS14) (h1614 := h_Step1614) (h1615 := h_Step1615)
    (hSz := h_Step1616OmegaSz)
  have h_Step1616 := CFSG.RankThree.PartTwo.Sec16.step1616_of (h1611 := h_Step1611)
    (h1614 := h_Step1614) (h1615 := h_Step1615) (hMeet := h_KS1615Meet) (hFix := h_Step1616Fix)
    (hComm := h_Step1616Comm) (hΩ := h_Step1616Omega)
  have h_Step1619One := CFSG.RankThree.PartTwo.Sec16.step1619One_of (h1614 := h_Step1614)
    (h1616 := h_Step1616) (h1510 := h_Item1510R) (hBr := h_Step169TwoBridge)
  have h_Claim17MR := CFSG.RankThree.PartTwo.Sec17.claim17MR_of (h163 := h_Item163R)
    (h152 := h_Item152R)
  have h_Step167TwoNonsolvR := CFSG.RankThree.PartTwo.Sec16.step167TwoNonsolvR_of
  have h_Step167VR := CFSG.RankThree.PartTwo.Sec16.step167VR_of_items (h163 := h_Item163R)
    (h1514 := h_Item1514R) (hMeets := h_Step163Meets) (h1444 := h_Item1444S14)
    (h146 := h_Item146S14) (hbot := h_Item145BotS14) (h142 := h_Concl142R)
  have h_Item164R := CFSG.RankThree.PartTwo.Sec16.item164R_of_route (h415 := h_Item4_15)
    (h131 := h_Item131) (hspor := h_SporadicModels131) (h138 := h_Item138N) (h1514 := h_Item1514R)
    (h163 := h_Item163R) (hMeets := h_Step163Meets)
  have h_Item145BotS17 := CFSG.RankThree.PartTwo.Sec14.item145BotS17_of (h := h_Item145BotS14)
  have h_Step171CommQ := CFSG.RankThree.PartTwo.Sec15.ThmC.step171CommQ_of_route_free
    (h148 := h_Item148R) (h142 := h_Concl142S14) (h146 := h_Item146S14) (h1444 := h_Item1444S14)
    (hbot := h_Item145BotS14)
  have h_Item1514S17 := CFSG.RankThree.PartTwo.Sec15.item1514S17_of_res (h131 := h_Item131)
    (h137 := h_Item137) (h1511 := h_Item1511S17) (h1513 := h_Item1513S17) (h148 := h_Item148R)
    (hbot := h_Item145BotS14) (h142 := h_Item142R) (h134 := h_Item134) (h48 := h_Item4_8)
    (h135 := h_Item135)
  have h_Claim1715Meets := CFSG.RankThree.PartTwo.Sec16.claim1715Meets_of (h := h_Step163Meets)
  have h_KS165U := CFSG.RankThree.PartTwo.Sec16.ks165U
  have h_KS165L := CFSG.RankThree.PartTwo.Sec16.ks165L
  have h_Res165R := CFSG.RankThree.PartTwo.Sec16.res165R_of_core (hRead := h_Y4CoreReadR)
    (hMem := h_Y4CoreMemR) (hbot := h_Item145BotS14)
  have h_Red165R := CFSG.RankThree.PartTwo.Sec16.red165R_of (hbot := h_Item145BotS17)
    (h146 := h_Item146S14) (h149 := h_Item149S14) (h142 := h_Concl142S14) (hRead := h_Y4CoreReadR)
    (h1514 := h_Item1514S17) (hMeets := h_Claim1715Meets)
  have h_Item165S17 := CFSG.RankThree.PartTwo.Sec16.item165S17_of_kfacts (hst := h_StellmacherKP)
    (hbot := h_Item145BotS17) (h146 := h_Item146S14) (h149 := h_Item149S14)
    (h153 := h_Item153MainR) (hQ := h_Step171CommQ) (h1514 := h_Item1514S17)
    (hMeets := h_Claim1715Meets) (h138 := h_Item138N) (hKU := h_KS165U) (hKL := h_KS165L)
    (hRes := h_Res165R) (hRed := h_Red165R)
  have h_Step167O2LocNot2nR := CFSG.RankThree.PartTwo.Sec16.step167O2LocNot2nR_of
    (h163 := h_Item163R) (h153 := h_Item153MainR)
  have h_Step167O2LocR := CFSG.RankThree.PartTwo.Sec16.step167O2LocR_of_not2n (h163 := h_Item163R)
    (h164 := h_Item164R) (hM := h_Claim17MR) (hMeets := h_Step163Meets) (h1514 := h_Item1514R)
    (h1510 := h_Item1510R) (hBr := h_Step169TwoBridge) (h165 := h_Item165S17)
    (hNot := h_Step167O2LocNot2nR)
  have h_Step167O2R := CFSG.RankThree.PartTwo.Sec16.step167O2R_of (h163 := h_Item163R)
    (hM := h_Claim17MR) (hT := h_Step167O2LocR)
  have h_Step1612Y3 := CFSG.RankThree.PartTwo.Sec16.step1612Y3_of (h152 := h_Item152R)
    (h142 := h_Item142R) (h135 := h_Item135Simple) (h138 := h_Item138N) (h1611 := h_Step1611)
    (hgen := h_Step1612Gen)
  have h_KS167D4 := CFSG.RankThree.PartTwo.KFacts.KS167D4Proof.ks167D4_holds
  have h_Step167EmptyO2R := CFSG.RankThree.PartTwo.Sec16.step167EmptyO2R_of (h138 := h_Item138N)
    (h149 := h_Item149S14) (h1612 := h_Step1612) (hD4 := h_KS167D4)
  have h_Step167EmptyFaithR := CFSG.RankThree.PartTwo.Sec16.step167EmptyFaithR_of_o2
    (h149 := h_Item149S14) (h146 := h_Item146S14) (h1610 := h_Step1610) (hY3 := h_Step1612Y3)
    (hO2 := h_Step167EmptyO2R)
  have h_Step167EmptyCentR := CFSG.RankThree.PartTwo.Sec16.step167EmptyCentR_of_faith
    (h138 := h_Item138N) (h1612 := h_Step1612) (hfaith := h_Step167EmptyFaithR)
  have h_Step167EmptyR := CFSG.RankThree.PartTwo.Sec16.step167EmptyR_of_cent (h149 := h_Item149S14)
    (h146 := h_Item146S14) (hcent := h_Step167EmptyCentR)
  have h_Item167R := CFSG.RankThree.PartTwo.Sec16.item167R_of (h149 := h_Item149S14)
    (h146 := h_Item146S14) (h153 := h_Item153MainR) (h163 := h_Item163R) (hM := h_Claim17MR)
    (hns := h_Step167TwoNonsolvR) (hV := h_Step167VR) (hO2 := h_Step167O2R)
    (hemp := h_Step167EmptyR)
  have h_KS1619SzFix := CFSG.RankThree.PartTwo.Sec16.ks1619SzFix
  have h_KSL3TwoIrrThree := CFSG.RankThree.PartTwo.Sec16.KL3SubProof.ksl3TwoIrrThree
  have h_KS1619LCen := CFSG.RankThree.PartTwo.Sec16.ks1619LCen_of_irrThree (hI := h_KSL3TwoIrrThree)
  have h_KS1619Sec := CFSG.RankThree.PartTwo.Sec16.ks1619Sec
  have h_Step1619CU := CFSG.RankThree.PartTwo.Sec16.step1619CU_proved (h138 := h_Item138N)
  have h_Step1619Two := CFSG.RankThree.PartTwo.Sec16.step1619Two_of_lcen (h1610 := h_Step1610)
    (h1612 := h_Step1612) (h1616 := h_Step1616) (h1619One := h_Step1619One) (h167 := h_Item167R)
    (hFix := h_KS1619SzFix) (hLCen := h_KS1619LCen) (hSec := h_KS1619Sec) (hCU := h_Step1619CU)
    (hbot := h_Item145BotS14)
  have h_Step1619 := CFSG.RankThree.PartTwo.Sec16.step1619_of (h1 := h_Step1619One)
    (h2 := h_Step1619Two)
  have h_Step169U38 := CFSG.RankThree.PartTwo.Sec16.step169U38_of_item138N (h138 := h_Item138N)
    (h1616 := h_Step1616)
  have h_Para1619At := CFSG.RankThree.PartTwo.Sec16.para1619At_of (h135 := h_Item135Simple)
    (h142 := h_Concl142R)
  have h_Para1619Five := CFSG.RankThree.PartTwo.Sec16.para1619Five_of_at (h := h_Para1619At)
  have h_Para1619 := CFSG.RankThree.PartTwo.Sec16.para1619_of_five (h := h_Para1619Five)
  have h_Step168OneZero := CFSG.RankThree.PartTwo.Sec17.step168OneZero_holds_of
    (h138 := h_Item138N) (h1612 := h_Step1612) (h146 := h_Item146S14)
  have h_Step168OneE := CFSG.RankThree.PartTwo.Sec17.step168OneE_of_zero (hst := h_StellmacherKP)
    (h146 := h_Item146S14) (h167 := h_Item167R) (hZ := h_Step168OneZero)
  have h_Step168NE := CFSG.RankThree.PartTwo.Sec17.step168NE_of_oneE (h146 := h_Item146S14)
    (hOne := h_Step168OneE)
  have h_Step168TwoE := CFSG.RankThree.PartTwo.Sec17.step168TwoE_of_oneE (h146 := h_Item146S14)
    (hOne := h_Step168OneE)
  have h_Item168REmpty := CFSG.RankThree.PartTwo.Sec17.item168REmpty_of (hst := h_StellmacherKP)
    (h146 := h_Item146S14) (h167 := h_Item167R) (hOne := h_Step168OneE) (hNot := h_Step168NE)
    (hTwo := h_Step168TwoE)
  have h_KS1617Fus := CFSG.RankThree.PartTwo.Sec16.ks1617Fus_proved
  have h_KS1620Gen := CFSG.RankThree.PartTwo.Sec16.kS1620Gen_of (hI := h_KSL3TwoIrrThree)
  have h_Step1620Gen := CFSG.RankThree.PartTwo.Sec16.step1620Gen_of (h138 := h_Item138N)
    (h1612 := h_Step1612) (h1619 := h_Step1619One) (hF := h_KS1617Fus) (hK := h_KS1620Gen)
  have h_Step1620 := CFSG.RankThree.PartTwo.Sec16.step1620_of_empty (h1610 := h_Step1610)
    (h1614 := h_Step1614) (h1616 := h_Step1616) (h1619 := h_Step1619) (h146 := h_Item146S14)
    (hbot := h_Item145BotS14) (h1411 := h_Item1411_3R) (h168E := h_Item168REmpty)
    (hGen := h_Step1620Gen)
  have h_Step1621Conj := CFSG.RankThree.PartTwo.Sec16.step1621Conj_of (h131 := h_Item131)
  have h_Step1621 := CFSG.RankThree.PartTwo.Sec16.step1621_of (h1616 := h_Step1616)
    (h1619 := h_Step1619) (hU38 := h_Step169U38) (hP := h_Para1619) (h1620 := h_Step1620)
    (hConj := h_Step1621Conj)
  have h_KS1623SU3Aut := CFSG.RankThree.PartTwo.Sec16.ks1623SU3Aut
  have h_Step1623NoTwo := CFSG.RankThree.PartTwo.Sec16.step1623NoTwo_of (h1612 := h_Step1612)
    (h138 := h_Item138N) (hK := h_KS1623SU3Aut)
  have h_Step1623EndS := CFSG.RankThree.PartTwo.Sec14.Ronan143Q.step1623EndS_of_item143Q
    (h143 := h_Item143QS14)
  have h_Step1623End := CFSG.RankThree.PartTwo.Sec16.step1623End_of_endS (hS := h_Step1623EndS)
  have h_Step1623 := CFSG.RankThree.PartTwo.Sec14.Ronan143Q.step1623_ofQ (h1612 := h_Step1612)
    (h1614 := h_Step1614) (h1616 := h_Step1616) (h1619One := h_Step1619One) (h1621 := h_Step1621)
    (h143 := h_Item143QS14) (hNoTwo := h_Step1623NoTwo) (hEnd := h_Step1623End)
  have h_KS1623Parab := CFSG.RankThree.PartTwo.Sec16.ks1623Parab
  have h_Para1623 := CFSG.RankThree.PartTwo.Sec16.para1623_of (h138 := h_Item138N)
    (hK := h_KS1623Parab)
  have h_KS1617E := CFSG.RankThree.PartTwo.Sec16.ks1617E_of_steps_two (h1614 := h_Step1614)
    (h1616 := h_Step1616) (h138 := h_Item138N)
  have h_Step1617 := CFSG.RankThree.PartTwo.Sec16.step1617_of (hE := h_KS1617E)
    (h138 := h_Item138N) (h1614 := h_Step1614)
  have h_KS1618Card := CFSG.RankThree.PartTwo.Sec16.ks1618Card_of_res8 (h1616 := h_Step1616)
    (h138 := h_Item138N)
  have h_Step1618Trans := CFSG.RankThree.PartTwo.Sec16.step1618Trans_of (h1616 := h_Step1616)
    (h138 := h_Item138N) (hCard := h_KS1618Card) (hF := h_KS1617Fus)
  have h_Step1618 := CFSG.RankThree.PartTwo.Sec16.step1618_of (h1614 := h_Step1614)
    (h1617 := h_Step1617) (hT := h_Step1618Trans)
  have h_K432InnerThree := CFSG.RankThree.PartTwo.Sec4.RonanK432.k432InnerThree_holds
  have h_K432List := CFSG.RankThree.PartTwo.Sec4.RonanK432.k432List_holds
  have h_Item4_32Comp := CFSG.RankThree.PartTwo.Sec4.item4_32Comp_of_three (hI := h_K432InnerThree)
    (hList := h_K432List)
  have h_KS1622GTwo := CFSG.RankThree.PartTwo.Sec16.ks1622GTwo
  have h_Step1622 := CFSG.RankThree.PartTwo.Sec16.step1622_of_comp (h1617 := h_Step1617)
    (h1618 := h_Step1618) (h432 := h_Item4_32Comp) (h41 := h_Item4_1LargePrime)
    (hG2 := h_KS1622GTwo)
  have h_SchreierCycThree := schreierCycThree_of_schreierFor
      CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds
  have h_Step1624 := CFSG.RankThree.PartTwo.Sec16.step1624_of_schreier (h1622 := h_Step1622)
    (h316 := h_Item316) (h1623 := h_Step1623) (hS := h_SchreierCycThree)
  have h_Step169PComm := CFSG.RankThree.PartTwo.Sec16.step169PComm_of_item138N
    (h135 := h_Item135Simple) (h138 := h_Item138N)
  have h_Step169EndFiveL316 := CFSG.RankThree.PartTwo.Sec14.Ronan143Q.step169EndFiveL316_of_cQ
    (h1622 := h_Step1622) (h316 := h_Item316) (h1623 := h_Step1623) (hS := h_SchreierCycThree)
    (h1614 := h_Step1614) (h1621 := h_Step1621) (h143 := h_Item143QS14) (h1423 := h_Item14_23R)
    (hPA := h_Step169PComm)
  have h_Item169R := CFSG.RankThree.PartTwo.Sec16.item169R_of_steps_fiveQ (h1614 := h_Step1614)
    (h1616 := h_Step1616) (h1619 := h_Step1619) (hU38 := h_Step169U38) (hP := h_Para1619Five)
    (h1621 := h_Step1621) (h1623 := h_Step1623) (hP23 := h_Para1623) (h1624 := h_Step1624)
    (h143 := h_Item143QS14) (h1423 := h_Item14_23R) (hPA := h_Step169PComm)
    (h5 := h_Step169EndFiveL316) (h163 := h_Item163R) (hMeets := h_Step163Meets)
    (h1514 := h_Item1514R) (h1510 := h_Item1510R) (hBr := h_Step169TwoBridge)
  have h_Step166KcdA5 := CFSG.RankThree.PartTwo.Sec16.Kcd166.step166KcdA5_holds
  have h_KG1 := CFSG.RankThree.PartTwo.J2Residue.kg1_holds
  have h_Step166KCommD := CFSG.RankThree.PartTwo.Sec16.Kd166.step166KCommD_of_kfacts
    (h143 := h_Item143QS14) (h134 := h_Item134) (h48 := h_Item4_8) (h1514 := h_Item1514S17)
    (hMeets := h_Claim1715Meets) (hG1 := h_KG1) (hfix := h_KJFix) (hsplit := h_KJSplit)
    (hcover := h_KJCover)
  have h_Item166S17 := CFSG.RankThree.PartTwo.Sec16.Ctr166.item166S17_of_leavesK
    (hst := h_StellmacherKP) (hExcl := h_Y4CoreExclSL25HJR) (h1523 := h_Item1523R)
    (h155 := h_Item155R) (h153 := h_Item153MainR) (h1514 := h_Item1514S17)
    (hMeets := h_Claim1715Meets) (hKcd := h_Step166KcdA5) (hKd := h_Step166KCommD)
  have h_Claim17Q0 := CFSG.RankThree.PartTwo.Sec17.claim17Q0_of_step171CommQ (hQ := h_Step171CommQ)
  have h_KS18A7M22 := CFSG.RankThree.PartTwo.KFacts.KS14.ks18A7M22
  have h_Item175R := CFSG.RankThree.PartTwo.Sec17.item175R_of (h169 := h_Item169R)
    (h163 := h_Item163R) (h164 := h_Item164R) (hM := h_Claim17MR) (h1514 := h_Item1514S17)
    (hMeets := h_Claim1715Meets) (h1511 := h_Item1511S17) (hA7 := h_KS18A7M22)
  have h_KS176GTwo := CFSG.RankThree.PartTwo.Sec17.ks176GTwo_holds
  have h_Step176Excl := CFSG.RankThree.PartTwo.Sec17.step176Excl_of (h1514 := h_Item1514S17)
    (hMeets := h_Claim1715Meets) (h1511 := h_Item1511S17) (hG2 := h_KS176GTwo)
  have h_Step176CommQ := CFSG.RankThree.PartTwo.Sec14.Ronan143Q.step176CommQ_of
    (hbal := h_Step143Balance)
  have h_Step176OdQ := CFSG.RankThree.PartTwo.Sec14.Ronan143Q.step176OdQ_of
    (hbal := h_Step143Balance)
  have h_Item176R := CFSG.RankThree.PartTwo.Sec14.Ronan143Q.item176R_of_compQ (h169 := h_Item169R)
    (h163 := h_Item163R) (h164 := h_Item164R) (hM := h_Claim17MR) (h175 := h_Item175R)
    (h432 := h_Item4_32Comp) (h41 := h_Item4_1LargePrime) (hexcl := h_Step176Excl)
    (h142 := h_Concl142S14) (h143c := h_Concl143S14) (hα := h_Step176CommQ) (hγ := h_Step176OdQ)
  have h_ProdLBarS17 := CFSG.RankThree.PartTwo.Sec17.Ronan17NoPGL.prodLBarS17_of_item1514
    (h131 := h_Item131) (h1514 := h_Item1514S17) (hMeets := h_Claim1715Meets)
  have h_CardInfNineS17 := CFSG.RankThree.PartTwo.Sec17.cardInfNineS17_of (h := h_ProdLBarS17)
  have h_KFactStar := Proof174Host.kfactStar_proved
      CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankCls.kFactThreeRankOneSimple
  have h_KFactL3Aut := F174L3Aut.Final.l3Aut_holds
  have h_Step168TwoOutNot2nOmega :=
    CFSG.RankThree.PartTwo.Sec17.Proof168Omega.step168TwoOutNot2nOmega_of_layer
    (hst := h_StellmacherKP) (h146 := h_Item146S14) (h149 := h_Item149S14) (h167 := h_Item167R)
    (h176 := h_Item176R) (h9 := h_CardInfNineS17) (hQ0 := h_Claim17Q0) (hStar := h_KFactStar)
    (hL3 := h_KFactL3Aut)
  have h_Step168TwoOutNot2n := CFSG.RankThree.PartTwo.Sec17.step168TwoOutNot2n_of_omega
    (hst := h_StellmacherKP) (h146 := h_Item146S14) (h167 := h_Item167R) (hQ0 := h_Claim17Q0)
    (h := h_Step168TwoOutNot2nOmega)
  have h_Item168S17 := CFSG.RankThree.PartTwo.Sec17.item168S17_of_not2n (hst := h_StellmacherKP)
    (h146 := h_Item146S14) (h167 := h_Item167R) (h166 := h_Item166S17) (hbot := h_Item145BotS17)
    (h165 := h_Item165S17) (hOut := h_Step168TwoOutNot2n)
  have h_Step171GenA10 := CFSG.RankThree.PartTwo.Sec17.step171GenA10_of (h1514 := h_Item1514S17)
    (hMeets := h_Claim1715Meets)
  have h_KFact171 := CFSG.RankThree.PartTwo.Sec17.kFact171_of (h1514 := h_Item1514S17)
    (hMeets := h_Claim1715Meets) (h142 := h_Concl142S14)
  have h_Step171Delta0 := CFSG.RankThree.PartTwo.Sec14.Ronan143Q.step171Delta0_ofQ
    (h422 := h_Item4_22) (h45 := h_Item4_5) (h142 := h_Item142R) (h143 := h_Item143QS14)
  have h_Step171Comm := CFSG.RankThree.PartTwo.Sec17.step171Comm_of (hQ := h_Step171CommQ)
    (hD0 := h_Step171Delta0)
  have h_Item171S17 := CFSG.RankThree.PartTwo.Sec17.item171S17_of (h1514 := h_Item1514S17)
    (hMeets := h_Claim1715Meets) (h142 := h_Concl142S14) (hGen := h_Step171GenA10)
    (hK := h_KFact171) (hComm := h_Step171Comm) (hD0 := h_Step171Delta0)
  have h_Step172PermPt := CFSG.RankThree.PartTwo.Sec17.Ronan172A.step172PermPt_of_items
    (h149 := h_Item149S14) (h142 := h_Item142R) (h175 := h_Item175R) (hbal := h_Step143Balance)
    (hMeets := h_Claim1715Meets) (h131 := h_Item131)
  have h_Step172Perm := CFSG.RankThree.PartTwo.Sec17.step172Perm_of (h142 := h_Item142R)
    (h175 := h_Item175R) (hbal := h_Step143Balance) (hpt := h_Step172PermPt)
  have h_Item172S17 := CFSG.RankThree.PartTwo.Sec17.item172S17_of (h171 := h_Item171S17)
    (h1514 := h_Item1514S17) (hperm := h_Step172Perm)
  have h_Claim1715A := CFSG.RankThree.PartTwo.Sec17.claim1715A_of
  have h_Step177Meet := CFSG.RankThree.PartTwo.Sec17.step177Meet_of_claim17Q0 (hQ0 := h_Claim17Q0)
  have h_KS1717J2Inner := CFSG.RankThree.PartTwo.Sec17.ks1717J2Inner
  have h_Item1411_1S17 := CFSG.RankThree.PartTwo.Sec14.item1411_1S17_holds
  have h_Item1714S17 := CFSG.RankThree.PartTwo.Sec17.item1714S17_of_inputs (h310 := h_Item3_10)
    (h135 := h_Item135) (h145 := h_Item145BotS14) (h146 := h_Item146S14) (h149 := h_Item149S14)
    (h1411 := h_Item1411_1S17) (h1514 := h_Item1514S17) (hMeets := h_Claim1715Meets)
    (h166 := h_Item166S17) (h167 := h_Item167R) (h168 := h_Item168S17) (h172 := h_Item172S17)
    (h176 := h_Item176R) (h9 := h_CardInfNineS17) (h1444 := h_Item1444S14) (h165 := h_Item165S17)
  have h_GriessMultipliersAllModels :=
    CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
  have h_Item1715 := CFSG.RankThree.PartTwo.Sec17.item1715_of_griess_named (h1514 := h_Item1514S17)
    (h1714 := h_Item1714S17) (hGA := h_GriessMultipliersAllModels) (hMeets := h_Claim1715Meets)
    (hAY := h_Claim1715A)
  have h_Item1717OneJ2Clause := CFSG.RankThree.PartTwo.Sec17.item1717OneJ2Clause_of
    (h1715 := h_Item1715) (h142 := h_Concl142S14)
  have h_Item1717OneL3J2 := CFSG.RankThree.PartTwo.Sec17.item1717OneL3J2_proof
    (hJ := h_KS1717J2Inner) (hJC := h_Item1717OneJ2Clause) (h1715 := h_Item1715)
    (h135 := h_Item135) (h142 := h_Concl142S14) (h166 := h_Item166S17) (hbot := h_Item145BotS17)
    (h168 := h_Item168S17) (h9 := h_CardInfNineS17) (h138 := h_Item138N)
  have h_Item1717One := CFSG.RankThree.PartTwo.Sec17.item1717One_of_L3J2
    (hRes := h_Item1717OneL3J2) (h1715 := h_Item1715) (h135 := h_Item135) (h142 := h_Concl142S14)
    (h166 := h_Item166S17) (hbot := h_Item145BotS17) (h168 := h_Item168S17) (h9 := h_CardInfNineS17)
  have h_Claim1720Inner := CFSG.RankThree.PartTwo.Sec17.claim1720Inner_of_one
    (h1717 := h_Item1717One) (h1715 := h_Item1715) (h142 := h_Concl142S14) (h166 := h_Item166S17)
    (hbot := h_Item145BotS17) (h168 := h_Item168S17)
  have h_Claim1720InnerL3 := CFSG.RankThree.PartTwo.Sec17.claim1720InnerL3_of
    (h := h_Claim1720Inner)
  have h_Item4_1PRankLargePrime :=
    CFSG.RankThree.PartTwo.Sec4.Item41Narrow.item4_1PRankLargePrime_of_griess
    (hGA := h_GriessMultipliersAllModels)
  have h_Claim1715Prime := CFSG.RankThree.PartTwo.Sec17.HeadProof.claim1715Prime_narrow
    (hP := h_Item4_1PRankLargePrime)
  have h_Claim174Inner := CFSG.RankThree.PartTwo.Sec17.claim174Inner_of_types
    (hL3 := h_Claim1720InnerL3) (hJ := h_KS1717J2Inner) (h1514 := h_Item1514S17)
    (hMeets := h_Claim1715Meets) (hPrime := h_Claim1715Prime) (h135 := h_Item135)
    (h142 := h_Concl142S14) (h166 := h_Item166S17) (hbot := h_Item145BotS17) (h168 := h_Item168S17)
    (h9 := h_CardInfNineS17) (h146 := h_Item146S14) (h1411 := h_Item1411_1S17)
  have h_Step174KbM := CFSG.RankThree.PartTwo.Sec14.Ronan143Q.step174KbM_of_res15Q
    (h166 := h_Item166S17) (h146 := h_Item146S14) (h45 := h_Item4_5) (h143 := h_Item143QS14)
    (h1514 := h_Item1514S17) (hMeets := h_Claim1715Meets)
  have h_Step174KbO := CFSG.RankThree.PartTwo.Sec17.step174KbO_of_kbM (h := h_Step174KbM)
  have h_Step177Contra := CFSG.RankThree.PartTwo.Sec17.step177Contra_of_res14
    (h171 := h_Item171S17) (hbal := h_Step143Balance) (h134 := h_Item134) (h48 := h_Item4_8)
    (h166 := h_Item166S17) (hbot := h_Item145BotS17) (h168 := h_Item168S17) (h146 := h_Item146S14)
    (h172 := h_Item172S17) (h9 := h_CardInfNineS17) (h165 := h_Item165S17) (hQ0 := h_Claim17Q0)
    (hI := h_Claim174Inner) (hKbO := h_Step174KbO)
  have h_Step177XbB := CFSG.RankThree.PartTwo.Sec17.step177XbB_of_contra (hC := h_Step177Contra)
    (hbal := h_Step143Balance) (h9 := h_CardInfNineS17)
  have h_Step177XbQuasi := CFSG.RankThree.PartTwo.Sec17.step177XbQuasi_of_contra
    (hC := h_Step177Contra) (hbal := h_Step143Balance) (h9 := h_CardInfNineS17)
  have h_Step177NRes := CFSG.RankThree.PartTwo.Sec17.step177NRes_of_contra (hC := h_Step177Contra)
    (hbal := h_Step143Balance) (h9 := h_CardInfNineS17)
  have h_Step177MainMB := CFSG.RankThree.PartTwo.Sec17.step177MainMB_of_parts (hB := h_Step177XbB)
    (hQ := h_Step177XbQuasi) (hres := h_Step177NRes)
  have h_Step177MainMAny := CFSG.RankThree.PartTwo.Sec17.step177MainMAny_of_MB
    (h := h_Step177MainMB)
  have h_Step177MainB := CFSG.RankThree.PartTwo.Sec17.step177MainB_of_any (h := h_Step177MainMAny)
  have h_Item177S17 := CFSG.RankThree.PartTwo.Sec17.item177S17_of_B (h310 := h_Item3_10)
    (h1514 := h_Item1514S17) (hMeets := h_Claim1715Meets) (hAY := h_Claim1715A)
    (h176 := h_Item176R) (hmeet := h_Step177Meet) (hmain := h_Step177MainB)
  have h_Item179S17 := CFSG.RankThree.PartTwo.Sec17.item179S17_of (h166 := h_Item166S17)
    (hbot := h_Item145BotS17) (h168 := h_Item168S17) (h146 := h_Item146S14) (h177 := h_Item177S17)
  have h_Step1711KM := CFSG.RankThree.PartTwo.Sec17.step1711KM_of_balance_meets_Q
    (hbal := h_Step143Balance) (h48 := h_Item4_8) (h1514 := h_Item1514S17)
    (hMeets := h_Claim1715Meets) (h134 := h_Item134)
  have h_Item1711S17 := CFSG.RankThree.PartTwo.Sec17.item1711S17_of_item166_concl143
    (h179 := h_Item179S17) (hKM := h_Step1711KM) (h422 := h_Item4_22) (h45 := h_Item4_5)
    (h142 := h_Item142R) (h143c := h_Concl143S14) (h166 := h_Item166S17)
  have h_Step177MainM := CFSG.RankThree.PartTwo.Sec17.step177MainM_of_any (h := h_Step177MainMAny)
  have h_Step1712SevenY0 := CFSG.RankThree.PartTwo.Sec17.step1712SevenY0_of_MB
    (hM := h_Step177MainMB) (h1514 := h_Item1514S17) (h176 := h_Item176R) (h9 := h_CardInfNineS17)
  have h_Step1712Seven := CFSG.RankThree.PartTwo.Sec17.step1712Seven_of_M (hmeet := h_Step177Meet)
    (hM := h_Step177MainM) (h1514 := h_Item1514S17) (h176 := h_Item176R) (h9 := h_CardInfNineS17)
    (hres := h_Step1712SevenY0)
  have h_Step1712Faith := CFSG.RankThree.PartTwo.Sec17.step1712Faith_of_items (h310 := h_Item3_10)
    (h9 := h_CardInfNineS17)
  have h_Step1712DeltaF := CFSG.RankThree.PartTwo.Sec17.Ronan1712Q8.step1712DeltaF_of_res14_faith
    (hFaith := h_Step1712Faith) (h1514 := h_Item1514S17) (hMeets := h_Claim1715Meets)
    (h176 := h_Item176R) (hbal := h_Step143Balance) (h143 := h_Item143QS14) (h166 := h_Item166S17)
    (hbot := h_Item145BotS17) (h168 := h_Item168S17) (h146 := h_Item146S14) (h172 := h_Item172S17)
    (h9 := h_CardInfNineS17) (h165 := h_Item165S17) (hQ0 := h_Claim17Q0) (hI := h_Claim174Inner)
    (hKbO := h_Step174KbO)
  have h_Step1712Delta := CFSG.RankThree.PartTwo.Sec17.step1712Delta_of_F (hF := h_Step1712DeltaF)
    (h166 := h_Item166S17) (hKM := h_Step1711KM)
  have h_Step1712Main := CFSG.RankThree.PartTwo.Sec17.step1712Main_of_items (h310 := h_Item3_10)
    (h9 := h_CardInfNineS17) (hD := h_Step1712Delta)
  have h_Item1712S17 := CFSG.RankThree.PartTwo.Sec17.item1712S17_of (h1711 := h_Item1711S17)
    (h7 := h_Step1712Seven) (hmain := h_Step1712Main)
  have h_Claim1719WNJOneL3 := CFSG.RankThree.PartTwo.Sec17.claim1719WNJOneL3_proof
    (h1715 := h_Item1715) (h135 := h_Item135) (h142 := h_Concl142S14) (h9 := h_CardInfNineS17)
    (h138 := h_Item138N)
  have h_Claim1719WNJ := CFSG.RankThree.PartTwo.Sec17.claim1719WNJ_of_L3
    (hL3 := h_Claim1719WNJOneL3) (h1715 := h_Item1715) (h135 := h_Item135) (h142 := h_Concl142S14)
    (h9 := h_CardInfNineS17)
  have h_Claim1719W := CFSG.RankThree.PartTwo.Sec17.claim1719W_of (h1715 := h_Item1715)
    (hNJ := h_Claim1719WNJ)
  have h_Claim1718QuotOneL3 := CFSG.RankThree.PartTwo.Sec17.claim1718QuotOneL3_proof
    (h1715 := h_Item1715) (h135 := h_Item135) (h142 := h_Concl142S14) (h9 := h_CardInfNineS17)
    (h138 := h_Item138N)
  have h_Claim1718QuotOne := CFSG.RankThree.PartTwo.Sec17.claim1718QuotOne_of_L3
    (hL3 := h_Claim1718QuotOneL3) (h1715 := h_Item1715) (h135 := h_Item135) (h142 := h_Concl142S14)
    (h9 := h_CardInfNineS17)
  have h_Claim1718QuotOneNA7 := CFSG.RankThree.PartTwo.Sec17.claim1718QuotOneNA7_of_one
    (h := h_Claim1718QuotOne)
  have h_Claim1718Quot := CFSG.RankThree.PartTwo.Sec17.claim1718Quot_of_nA7
    (hN := h_Claim1718QuotOneNA7) (h1715 := h_Item1715) (h135 := h_Item135) (h142 := h_Concl142S14)
    (h9 := h_CardInfNineS17)
  have h_Claim1718 := CFSG.RankThree.PartTwo.Sec17.claim1718_of (hQ := h_Claim1718Quot)
    (hQ0 := h_Claim17Q0) (h146 := h_Item146S14) (h166 := h_Item166S17) (hbot := h_Item145BotS17)
    (h168 := h_Item168S17)
  have h_Item1718 := CFSG.RankThree.PartTwo.Sec17.item1718_of (hC := h_Claim1718)
  have h_Item1710S17 := CFSG.RankThree.PartTwo.Sec17.item1710S17_of (h166 := h_Item166S17)
    (hbot := h_Item145BotS17) (h168 := h_Item168S17) (h179 := h_Item179S17)
  have h_Item1719 := CFSG.RankThree.PartTwo.Sec17.item1719_of_named (hW := h_Claim1719W)
    (h1718 := h_Item1718) (h1712 := h_Item1712S17) (h1710 := h_Item1710S17) (h166 := h_Item166S17)
    (hbot := h_Item145BotS17) (h9 := h_CardInfNineS17)
  have h_Claim1716Odd := CFSG.RankThree.PartTwo.Sec17.claim1716Odd_proof (h9 := h_CardInfNineS17)
  have h_Claim1720 := CFSG.RankThree.PartTwo.Sec17.claim1720_of_one (h1717 := h_Item1717One)
    (h1715 := h_Item1715) (h142 := h_Concl142S14) (hQ := h_Step171CommQ) (hOdd := h_Claim1716Odd)
    (h146 := h_Item146S14) (hbot := h_Item145BotS17) (h166 := h_Item166S17) (h168 := h_Item168S17)
  have h_Claim1721SylL3 := CFSG.RankThree.PartTwo.Sec17.claim1721SylL3_of (h1715 := h_Item1715)
    (h138 := h_Item138N)
  have h_KS1721AutThreeL3 := CFSG.RankThree.PartTwo.Sec17.ks1721AutThreeL3
  have h_Claim1721SCommL3 := CFSG.RankThree.PartTwo.Sec17.claim1721SCommL3_of
    (h1511 := h_Item1511S17) (hMeets := h_Claim1715Meets) (hSyl := h_Claim1721SylL3)
    (h9 := h_CardInfNineS17) (hK := h_KS1721AutThreeL3)
  have h_Item1721 := CFSG.RankThree.PartTwo.Sec17.item1721_of_one (h166 := h_Item166S17)
    (hbot := h_Item145BotS17) (h168 := h_Item168S17) (h146 := h_Item146S14)
    (h9 := h_CardInfNineS17) (h1719 := h_Item1719) (h1720 := h_Claim1720) (h1717 := h_Item1717One)
    (h1715 := h_Item1715) (h142 := h_Concl142S14) (hQ := h_Step171CommQ) (h138 := h_Item138N)
    (h175 := h_Item175R) (hcomm := h_Claim1721SCommL3) (hloc := h_Claim1411LocalR)
  have h_Para1722 := CFSG.RankThree.PartTwo.Sec17.para1722_of_items (h1715 := h_Item1715)
    (h1721 := h_Item1721)
  have h_Claim1722XThree := CFSG.RankThree.PartTwo.Sec17.claim1722XThree_of_j2
    (h1721 := h_Item1721) (h1514 := h_Item1514S17) (hMeets := h_Claim1715Meets)
    (h166 := h_Item166S17) (h168 := h_Item168S17) (hbot := h_Item145BotS17)
  have h_Claim1722X := CFSG.RankThree.PartTwo.Sec17.claim1722X_of (hX3 := h_Claim1722XThree)
    (h146 := h_Item146S14) (h166 := h_Item166S17) (h168 := h_Item168S17) (h179 := h_Item179S17)
    (hbot := h_Item145BotS17)
  have h_KS17J2CentralizerNine := KFacts.ks17J2CentralizerNine
  have h_Claim1722T := CFSG.RankThree.PartTwo.Sec17.claim1722T_of (hK := h_KS17J2CentralizerNine)
    (h1721 := h_Item1721)
  have h_Item1722 := CFSG.RankThree.PartTwo.Sec17.item1722_of (h166 := h_Item166S17)
    (hbot := h_Item145BotS17) (h168 := h_Item168S17) (hX := h_Claim1722X) (hT := h_Claim1722T)
    (h1720 := h_Claim1720)
  have h_Claim1723Orbit := CFSG.RankThree.PartTwo.Sec17.claim1723Orbit_of (h1715 := h_Item1715)
    (h1721 := h_Item1721)
  have h_Item1723N := CFSG.RankThree.PartTwo.Sec17.Proof1721.item1723N_of (h166 := h_Item166S17)
    (hbot := h_Item145BotS17) (h168 := h_Item168S17) (h1411 := h_Item1411_1S17)
    (h1718 := h_Item1718) (h1720 := h_Claim1720) (h1722 := h_Item1722) (horb := h_Claim1723Orbit)
  have h_Item1724NormThreePrime := CFSG.RankThree.PartTwo.Sec17.item1724NormThreePrime_of_inputs
    (h148 := h_Item148R) (hbal := h_Step143Balance) (h1514 := h_Item1514S17)
    (hMeets := h_Claim1715Meets)
  have h_Item1724LocR := CFSG.RankThree.PartTwo.Sec17.item1724LocR_of (h1721 := h_Item1721)
    (h1514 := h_Item1514S17) (hMeets := h_Claim1715Meets) (hbal := h_Step143Balance)
    (hnorm := h_Item1724NormThreePrime)
  have h_Item1724LocN := CFSG.RankThree.PartTwo.Sec17.item1724LocN_of_R (hR := h_Item1724LocR)
    (h146 := h_Item146S14) (hbot := h_Item145BotS14)
  have h_Claim1724DeltaMeet := CFSG.RankThree.PartTwo.Sec17.claim1724DeltaMeet_of
    (h1514 := h_Item1514S17) (hMeets := h_Claim1715Meets)
  have h_J2NotSectionOfGLFourTwo := CFSG.RankThree.PartTwo.Sec17.j2NotSectionOfGLFourTwo_holds
  have h_J2CoverHasElemAbelianEight :=
    CFSG.RankThree.PartTwo.Sec17.J2CoverE8.j2CoverHasElemAbelianEight_holds
  have h_Claim1724DeltaMax := CFSG.RankThree.PartTwo.Sec17.claim1724DeltaMax_of_inputs
    (h1514 := h_Item1514S17) (hMeets := h_Claim1715Meets) (hbot := h_Item145BotS17)
    (h148 := h_Item148HJS14) (h149 := h_Item149S14) (h152 := h_Item152R) (h155 := h_Item155R)
    (hFT := h_J2NotSectionOfGLFourTwo) (hCover := h_J2CoverHasElemAbelianEight)
  have h_Claim1724Delta := CFSG.RankThree.PartTwo.Sec17.claim1724Delta_of (h1721 := h_Item1721)
    (hmeet := h_Claim1724DeltaMeet) (hmax := h_Claim1724DeltaMax)
  have h_Claim17O2Y0 := CFSG.RankThree.PartTwo.Sec17.claim17O2Y0_of (hQ := h_Step171CommQ)
    (h146 := h_Item146S14) (h166 := h_Item166S17) (h168 := h_Item168S17) (hbot := h_Item145BotS17)
  have h_Item1724N := CFSG.RankThree.PartTwo.Sec17.item1724N_of_res (hloc := h_Item1724LocN)
    (hΔ := h_Claim1724Delta) (hO2 := h_Claim17O2Y0) (h146 := h_Item146S14) (h166 := h_Item166S17)
    (hbot := h_Item145BotS17) (h179 := h_Item179S17)
  exact item1730_of_routeS16_narrowQ_1723N (h142N := h_Concl142NHJS14) (h143c := h_Concl143S14)
    (h143 := h_Item143NNHJ) (h1444 := h_Item1444S14) (h148 := h_Item148R)
    (hW1411 := h_Claim1411NonsolvWR) (hX1411 := h_Claim1411NonsolvXR) (hcomp := h_Step152CompR)
    (hexcl := h_Step152ExclR) (hconf := h_Step152ConfR) (hend := h_Step152EndR)
    (h1515 := h_Step1515S17) (h1519 := h_Step1519S17) (h1521 := h_Step1521S17)
    (h1522 := h_Step1522S17) (h1514 := h_Item1514R) (h1523 := h_Item1523R) (h153 := h_Item153MainR)
    (hobs := h_Claim153ObsR) (hn := h_Claim153NormalR) (h155 := h_Item155R)
    (h142All := h_Item142AllS14) (h148S := h_Item148SmallS14) (hCore := h_Step148Core)
    (hPoint := h_Step148Point) (hKT := h_Step148KType) (hMem := h_Y4CoreMemR) (h135 := h_Item135)
    (h1424 := h_Item14_24R) (h1510 := h_Item1510R) (h135S := h_Item135Simple) (h138 := h_Item138N)
    (h169 := h_Item169R) (h165 := h_Item165S17) (h166 := h_Item166S17) (h168 := h_Item168S17)
    (h172 := h_Item172S17) (h175 := h_Item175R) (h176 := h_Item176R) (h177 := h_Item177S17)
    (h1712 := h_Item1712S17) (hprod := h_ProdLBarS17) (hW1722 := h_Para1722)
    (hMeets := h_Claim1715Meets) (hAY := h_Claim1715A) (hW1719 := h_Claim1719W)
    (hC1718 := h_Claim1718) (h1721 := h_Item1721) (h1723 := h_Item1723N) (h1724 := h_Item1724N)
    (h134 := h_Item134) (hP := h_Item4_1PRankLargePrime) (h48 := h_Item4_8)
    (hst := h_StellmacherKP) (hgen := h_KS152HJGen) (h131 := h_Item131)

end CFSG.RankThree.PartTwo.Sec14.Ronan143Q
