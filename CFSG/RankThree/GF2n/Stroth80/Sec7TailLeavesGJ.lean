module

public import CFSG.RankThree.GF2n.Stroth80.Sec7WVNe6Om4
public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsVanish
public import CFSG.RankThree.GF2n.Stroth80.Sec7SylowLB
public import CFSG.RankThree.GF2n.Stroth80.Sec7CardAlpha
public import CFSG.RankThree.GF2n.Stroth80.Step78Ineq
public import CFSG.RankThree.GF2n.Stroth80.Sec7WVGe
public import CFSG.RankThree.GF2n.Stroth80.Step76NoWildSix
public import CFSG.RankThree.GF2n.Stroth80.Step710VanishProof
public import CFSG.RankThree.GF2n.Stroth80.Sec78ConjOm4
public import CFSG.RankThree.GF2n.Stroth80.Sec7BorelRankOne
public import CFSG.RankThree.GF2n.Stroth80.StatedOmegaPerfect
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailCaseOne
public import CFSG.RankThree.GF2n.Stroth80.Sec717LNatural
public import CFSG.RankThree.GF2n.Stroth80.Sec717LayerWedgeTyping
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailNotUnitary
public import CFSG.RankThree.GF2n.Stroth80.QuadraticPlusTypeDickson
public import CFSG.RankThree.GF2n.Stroth80.Sec7Index72
public import CFSG.RankThree.GF2n.Stroth80.Sec716NoLargeUnitary
public import CFSG.RankThree.GF2n.Stroth80.Sec7EightTamePoint
public import CFSG.RankThree.GF2n.Stroth80.Sec7Step77Moves
public import CFSG.RankThree.GF2n.Stroth80.Sec717WCProof
public import CFSG.RankThree.GF2n.Stroth80.Sec7EightWildMeet
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailNotUnitaryLevi
public import CFSG.RankThree.GF2n.Stroth80.Sec7Om10
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailRadicalLinear
public import CFSG.RankThree.GF2n.Stroth80.Sec7EightSmithCore
public import CFSG.RankThree.GF2n.Stroth80.Sec715ZNModel
public import CFSG.RankThree.GF2n.Stroth80.Sec714ModelN12
public import CFSG.RankThree.GF2n.Stroth80.Sec717MoveRepOfLayers
public import CFSG.RankThree.GF2n.Stroth80.Sec717CRSylowProof
public import CFSG.RankThree.GF2n.Stroth80.IrrQ4Holds
public import CFSG.RankThree.GF2n.Stroth80.Sec717InvolutionProof
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailRadicalRankTwo
public import CFSG.RankThree.GF2n.Stroth80.Sec713O2Coprime
public import CFSG.RankThree.GF2n.Stroth80.Sec713O2CentreFix
public import CFSG.RankThree.GF2n.Stroth80.Sec713O2CentralN
public import CFSG.RankThree.GF2n.Stroth80.Sec7Step77TameComm
public import CFSG.RankThree.GF2n.Stroth80.Sec715ZNComm
public import CFSG.RankThree.GF2n.Stroth80.Sec717QLayersMain
public import CFSG.RankThree.GF2n.Stroth80.Sec717RSylowIndep
public import CFSG.RankThree.GF2n.Stroth80.Sec717SL4W3Holds
public import CFSG.RankThree.GF2n.Stroth80.Sec717SL4HomHolds
public import CFSG.RankThree.GF2n.Stroth80.Sec717NbarKStructure
public import CFSG.RankThree.GF2n.Stroth80.Sec715IrrStepsCited
public import CFSG.RankThree.GF2n.Stroth80.Sec715IrrAWrap
public import CFSG.RankThree.GF2n.Stroth80.Sec715IrrAWrap2
public import CFSG.RankThree.GF2n.Stroth80.Sec7VanishGeomOm4
public import CFSG.RankThree.GF2n.Stroth80.Sec715Ext1Holds
public import CFSG.RankThree.GF2n.Stroth80.Omega8SmallHolds
public import CFSG.RankThree.GF2n.Stroth80.Sec715TriFinal

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

structure Sec7TailLeavesGJ : Prop where
  cor2 : Tim77Cor2Statement
  outSolvAlpha : OutSolvableAlphaStatement
  corB : CorollaryBStmt
  outSolv : OutSolvableListStatement
  twoRank : TwoRankSporadicAltStatement
  outSolvU6 : OutSolvableUnitarySixStatement
  tim81unRoot : Tim81StrothUnRootStatement

section Assembly

theorem sec7Tail_of_leavesGJ (L : Sec7TailLeavesGJ) :
    Stroth78Statement ∧ Stroth79Statement ∧ Stroth716TypeStatement ∧ Stroth717Statement := by
  have h34 : Stroth34Statement := stroth34Statement_unconditional
  have h310 : Stroth310Statement := stroth310Statement_unconditional
  have h311a : Stroth311aStatement := stroth311aStatement_unconditional
  have h44 : Stroth44Statement := stroth44Statement_unconditional
  have h45 : Stroth45Statement := stroth45Statement_unconditional
  have h51 : Stroth51Statement := stroth51Statement_unconditional
  have aEx : Sec7AExistsStatement := sec7AExistsStatement_unconditional
  have aEx8 : Sec8AExistsStatement := sec8AExistsStatement_unconditional
  have h52a : Stroth52aStatement := stroth52aStatement_holds
  have h52b : Stroth52bStatement := stroth52bStatement_holds
  have h310chi : Stroth310ChiStatement := stroth310Chi_of_34 h34
  have h310root : Stroth310RootStatement := stroth310Root_of_34 h34
  have h56 : Stroth56NatStatement := stroth56Nat_of_34 h34
  have hpts : Sec5NatPointsOmegaStatement := sec5NatPointsOmega_of h34 h310root
  have hptsSp : Sec5NatPointsSpStatement := sec5NatPointsSp_of h34 h310root
  have sec713Y : Sec713YStatement := sec713Y_of_inputs h34 h311a h51 aEx hpts
  have h52c : Stroth52cStatement := stroth_5_2c_of_chi h310chi
  have centre : Sec7CentreMpStatement := sec7CentreMp_of_inputs h51 h52a aEx
  have zt : Sec7ZtStatement :=
    sec7Zt_of_inputs h34 h310 h51 h52a aEx aEx8 h56 hpts hptsSp
  have cv : Sec7CVStatement := sec7CV_of_inputs h34 h310root aEx h52b
  have conjOm4 : Sec7ConjOm4Statement := sec7ConjOm4_of_inputs h34 aEx hpts zt
  have zcard : Sec7ZCardStatement := sec7ZCard_of_inputs h51 aEx
  have hZV : Sec7ZVStatement := sec7ZV_of_parts zt centre h310chi
  have om4Base : Stroth73aOm4BaseStatement :=
    stroth73aOm4Base_of_psi h34 h310chi centre hZV zcard
      (stroth73aOm4PsiCore_of h34 h310root)
  have hSch : Sec7SchurStatement := sec7Schur_of_parts h34 h310chi centre hZV zcard
  have hK : Sec7CRWStatement := sec7CRW_of_inputs h34 h310chi h51 h52a aEx hSch
  have nOrder : Sec7NOrderStatement := sec7NOrder_of h34 h51 aEx hpts
  have wvOrder : Sec7WVOrderStatement :=
    sec7WVOrder_of nOrder h52a h52b h52c aEx hpts
  have wvGe : Sec7WVGeStatement := sec7WVGe_of h34 wvOrder aEx hpts h52a h52b h52c
  have wvGeOm4 : Sec7WVGeOm4Statement :=
    sec7WVGeOm4_of wvOrder (sec7WVNe6Om4_of h34 aEx hpts h52a h52b h52c)
  have step78Ineq : Step78IneqStatement := step78Ineq_of aEx hpts h52a h52b h52c hZV
  have minOrder : Sec79MinOrderStatement := sec79MinOrder_of h51 aEx hpts
  have hNR : Sec7NormZ0Statement := sec7NormZ0_of_inputs h56 aEx
  have hNC : Sec7ConjStatement := sec7Conj_of_parts h56 centre zt
  have h73a : Stroth73aStatement :=
    stroth73a_of_cases (stroth73aNotOm4_of hNR) (stroth73aOm4_of_base zt centre om4Base)
  have hcard : Sec73CardStatement :=
    sec73Card_of_parts (sec73CardAlpha_of_inputs h34 h310root h52a aEx h310chi)
      (sec73CardBeta_of_inputs aEx hpts h52a h52b h310chi) wvGeOm4
  have h73cOm4 : Stroth73cOm4Statement := stroth73cOm4_of h73a cv hcard conjOm4
  have h72 : Stroth72Statement :=
    stroth72_of_index (sec7CommN_of_34 h34 h310 h311a) zcard
      (step72Index_of_inputs h34 h310root h52a h52b aEx hpts hZV cv hNC conjOm4 om4Base
        hNR)
  have h73b : Stroth73bStatement := stroth73b_of_72 h72 h73a hZV zt centre hNC conjOm4
  have hTr : Stroth73bTransStatement := stroth73bTrans_of h73b hNC conjOm4
  have sylowLB : Sec7SylowLBStatement := sec7SylowLB_of_34 h34
  have hEnd : Sec7EndStatement :=
    sec7End_of_parts h34 h310chi zt centre zcard h311a h44 h45
  have hPair : Step71VanishPairStatement :=
    step71VanishPair_of_omega4 h34 h310root h310chi centre hZV zcard omegaMinusFourGeom_holds
      omegaMinusFourSingularTrans_holds
  have hV : Step71VanishStatement :=
    step71Vanish_of_steps (step71VanishBound_of_pair hPair h52b h310chi) wvOrder
      wvGeOm4 wvGe
      (step71VanishOmega10_of h34 h310root h52a h52b hPair centre hZV zcard)
  have hT : Step71TypeStatement :=
    step71Type_of_steps hV (step71TypeSec_of_inputs h52a h52b aEx h310chi hpts)
      (sec7WVSecOrder_of_points hpts)
  have q7 : Sec7Q7Statement :=
    sec7Q7_of_kernel aEx h34 h310root h52a h52b cv
      (sec7Q7Kernel_of_inputs h34 h310root)
  have h71 : Stroth71Statement :=
    stroth71_of_steps hV hT
      (step71close_of_parts (close71TI_of h73a hZV)
        (close71Sylow_of_parts h34 h310chi h311a hZV h73a q7)
        (close71E_of_parts h34 h310chi centre hZV hK hSch h52a aEx hV)
        (close71Final_of_end hEnd))
  have hSec : Sec7WVSecCardStatement := sec7WVSecCard_of aEx hpts h52a h52b
  have step77One : Step77OneStatement := step77One_of_notNorm
    (step77OneNotNorm_of_inputs h34 h310root h71 h310chi centre hZV zcard h52a aEx hSec
      hK h73a h73cOm4 cv sec7VtIrred_holds) om4Base
  have step77FromOne : Step77FromOneStatement := step77FromOne_of_core
    (step77FromOneCore_of_stmts h34 h310root h71 h310chi centre hZV zcard h52a h52b
      aEx hpts)
  have noWildSix : Step76NoWildSixCoreStatement :=
    step76NoWildSixCore_of h34 aEx hpts h52a h52b h310chi hV
  have eightTW : Step76EightKTameWildStatement := step76EightKTameWild_of
    (step76EightTameConj_of_point (step76EightTamePoint_of h34 h310root hZV) h56)
      (step76EightKTame_of_smith_core h34 h310root h310chi h71 centre hZV zcard h52a aEx
        hSec hV
        (step76EightSmithCore_of h34 h310root h310chi h71 centre hZV zcard h52a aEx
          hSec hV (sec7WVSplit_of aEx hpts h52a h52b) smithOmegaPlusEight_holds))
  have eightWW : Step76EightKWildWildStatement :=
    step76EightKWildWild_of_witness h52a aEx h310chi hSec h71 hZV
      (step76EightWildWitness_of_moves_meet h34 h310chi h71 centre hZV zcard h52a aEx
        hSec
        (step76EightWildMoves_of_inputs h34 h71 h310chi centre hZV zcard h52a aEx hpts
          (sec7WVSplit_of aEx hpts h52a h52b))
        (step76EightWildMeet_of_inputs h34 h71 h310chi centre hZV zcard h52a aEx))
      eightTW
  have step76E : Step76EStatement :=
    step76E_of_cases h71 (step76NoWildSix_of h71 noWildSix)
      (step76Eight_of_K (step76EightK_of_parts eightTW eightWW)
        h34 h310chi centre hZV zcard hK hSch h52a aEx hV)
  have h76 : Stroth76Statement := stroth76_of_steps hNR centre hZV hTr sylowLB step76E hEnd
  have h73c : Stroth73cStatement := stroth73c_of_cases (stroth73cNotOm4_of h73a hNC cv) h73cOm4
  have h77 : Stroth77Statement :=
    stroth77_of_steps h76 h71 h73c centre step77One
      (step77Two_of_one step77One step77FromOne) (step77End_of_one step77One step77FromOne)
  have h78 : Stroth78Statement := stroth78_of_inputs h77 nOrder wvOrder step78Ineq wvGe
  have h79 : Stroth79Statement := stroth79_of_inputs h78 h51 aEx zcard minOrder
  have h710 : Stroth710Statement :=
    stroth710_of_steps h34 h77 centre hNR hZV hNC conjOm4
      (step710E_of_inputs h34 h310root h310chi h77 centre hZV zcard hNC hK hSch aEx hpts
        h52a h52b h56) sylowLB hEnd
  have h711S : Stroth711StrongStatement :=
    stroth711Strong_holds h34 h310root h52a nOrder aEx
  have h714 : Stroth714Statement :=
    stroth714_of_inputs h78
      (step714NotTwelve_of_model
        (S714.sec714Model_of
          ⟨h34, h310root, h310chi, h51, h52a, h52b, nOrder, zcard, hK, centre, hZV⟩
          h711S aEx hpts)
        statedOmegaPlusFourPerfect_holds (quadraticPlusType_of_dickson dicksonOmegaPlusFour_holds))
  have hCommN : Sec7CommNStatement := sec7CommN_of_34 h34 h310 h311a
  have zn717 : Sec717ZNStatement :=
    sec717ZN_of_parts h51 aEx hpts h78 zcard hCommN h711S irrQ4NoPairing_holds
  have h712 : Stroth712Statement := stroth712_holds h34 h51 aEx zt zcard
  have cent715 : Sec715CentStatement :=
    sec715Cent_of_parts h34 h310chi h51 h52a aEx zcard sec7VtIrred_holds cv hSch
  have ext1D4 : Ext1VanishingD4Statement :=
    S715L.ext1VanishingD4_of h34 h310root h51 h52a h52b nOrder zcard hK centre aEx hpts
  have tri : Omega8TrialityStatement := Tri.omega8Triality_of_smallNF Tri.smallNF_holds
  have hLS : S715L.Sec715LayerSplitStatement :=
    S715L.sec715LayerSplit_of stroth34Statement_unconditional stroth310RootStatement_unconditional
        (stroth310Chi_of_34 stroth34Statement_unconditional) stroth51Statement_unconditional
        stroth52aStatement_holds stroth52bStatement_holds sec7NOrderStatement_holds
        sec7ZCardStatement_holds sec7CRWStatement_holds sec7CentreMpStatement_holds
        sec7CVStatement_holds sec7AExistsStatement_unconditional ext1D4 omega8LongRootRank_holds
        (sec7WVMinOrder_of sec7AExistsStatement_unconditional
            sec5NatPointsOmegaStatement_unconditional stroth52aStatement_holds
            stroth52bStatement_holds)
        (sec79MinOrder_of stroth51Statement_unconditional sec7AExistsStatement_unconditional
            sec5NatPointsOmegaStatement_unconditional)
  have conj715 : Sec715ConjStatement := sec715Conj_of_layerSplit hLS cent715 h710
  have irr715 : Sec715IrrStatement :=
    S715L.sec715Irr_of_steps ext1D4 omega8LongRootRank_holds tri omega8EndScalar_holds h710
      (S715L.sec715NonOrthNbrs_of h77 (sec715Adj_of hLS cent715) cent715 h34 h311a zt zcard hZV
        centre h310root h310chi h51 h52a h52b nOrder hK hCommN)
      (S715L.sec715HasLine_of tri h310chi h52a centre hK zcard)
      (S715L.sec715SameLineOrth_of tri omega8EndScalar_holds h34 h310root h310chi h51 h52a h52b
        nOrder aEx zt zcard hZV hCommN sec713Y cent715 hK centre)
      (S715L.sec715RootElt_of tri omega8EndScalar_holds h34 h310root h310chi h51 h52a h52b nOrder
        aEx zt zcard hZV hCommN sec713Y cent715 hK centre)
  have h715 : Stroth715Statement := stroth715_of_steps
    (step715ZN_of_model
      (sec715ZNModel_of h34 h310root h310chi h51 h52a h52b nOrder zcard hK centre hCommN
        aEx hpts h711S)
      (sec715Split_of_comm (sec715ZNComm_holds h51 aEx hpts nOrder h711S) h51
        aEx hpts) h714
      h711S statedOmegaPlusFourPerfect_holds
      (quadraticPlusType_of_dickson dicksonOmegaPlusFour_holds))
    (step715Hyp79_of_parts h34 h310chi h311a h51 aEx zt zcard centre hZV hNR hCommN
      h711S h712 h714 sec713Y cent715 conj715 irr715)
  have hHard : Step713O2HardStatement :=
    step713O2Hard_of_steps
      (step713XActs_of h52a h52b (stroth_5_2c_of_chi h310chi) aEx hpts h310chi zt zcard
          (sec7WVSecOrder_of_points hpts) h78
          (step713XActsPlus6_of h34 aEx hpts h52a h52b h310chi zt zcard))
      (step713Coprime_of h34 h311a h51 aEx hpts zt zcard h310chi h52a hK)
      (step713CentralN_of h79 zn717 h711S hSch h34 h51 h52a aEx zcard)
      (step713CentreFix_of centre hZV)
  have h713 : Stroth713Statement :=
    stroth713_of_steps h712 (step713O2_of_hard h34 h51 aEx zt zcard hHard)
  have hNL : Sec7NormLB'Statement := sec7NormLB'_of_710 h34 h311a h710 hNC conjOm4 zt zcard
  have hSub : Step7HypSub'Statement := step7HypSub_of_parts h34 h311a zt zcard centre
  have inv717 : Sec717InvStatement :=
    sec717Inv_of_parts h51 aEx hpts h78 zcard hCommN irrQ4NoPairing_holds
  have typing717 : Sec717LTypingStatement :=
    sec717LTyping_of_kstruct h34 h311a zt zcard centre h78 hZV h52a aEx
        (sec717NbarKStructure_of stroth34Statement_unconditional
            stroth310RootStatement_unconditional stroth51Statement_unconditional stroth52aStatement_holds
            stroth52bStatement_holds sec7NOrderStatement_holds sec7ZCardStatement_holds
            sec7CRWStatement_holds sec7CentreMpStatement_holds sec7AExistsStatement_unconditional
            sec7ZVStatement_holds)
      inv717
  have wedge717 : Sec717LayerWedgeStatement :=
    sec717LayerWedge_of_typing typing717 zcard centre hZV
  have qLayers717 : Sec717QLayersStatement :=
    sec717QLayers_of_layerModel h34 h311a zt zcard centre h78 hZV h52a aEx
      (sec717NbarKStructure_of stroth34Statement_unconditional stroth310RootStatement_unconditional
          stroth51Statement_unconditional stroth52aStatement_holds stroth52bStatement_holds
          sec7NOrderStatement_holds sec7ZCardStatement_holds sec7CRWStatement_holds
          sec7CentreMpStatement_holds sec7AExistsStatement_unconditional sec7ZVStatement_holds) wedge717 sl4HomW3_holds sl4NoInvForm_holds
  have rSylow717 : Sec717RSylowStatement :=
    sec717RSylow_indep h34 h311a zt zcard centre h78 hZV h52a h52b aEx hpts cent715
      hHard wedge717
  have caseOne717 : Sec717CaseOneStatement :=
    sec717CaseOne_of_inputs h34 h311a h51 aEx zt zcard centre h78 hCommN sec713Y
      L.cor2 L.outSolv L.outSolvAlpha L.twoRank borelRankOneSolvable_holds artinLinearOrders_holds
      radicalTwoSubgroupLinearStatement_holds radicalTwoSubgroupRankTwoStatement_holds
  have frame717 : Sec717MoveFrameStatement :=
    sec717MoveFrame_of_rep h34 h311a zt zcard centre h78 hZV hCommN
      (sec717MoveRep_of_layers h34 h311a zt zcard centre h78 hZV hCommN h52a aEx
        inv717 qLayers717 rSylow717)
  have norm717 : Sec717NormalizeStatement := sec717Normalize_of_sylow frame717
    (sec717NormSylow_of_parts frame717 rSylow717
      (sec717CRSylow_of_orbitOdd frame717 h34 centre hZV
        (sec717OrbitOdd_of_typing hCommN typing717)))
  have corBHyp717 : Sec717CorBHypStatement :=
    sec717CorBHyp_of_parts h51 aEx hpts hCommN centre zcard
      (sec717Involution_of_frame frame717 inv717) norm717
      (sec717WC_of_frame frame717 norm717)
  have hA : Step717CaseAStatement :=
    step717CaseA_of_parts h34 h311a zt zcard hNR hZV h713 zn717 cent715 caseOne717
      (sec717Move_of_frame frame717) corBHyp717
      (sec717Recog_of_inputs h34 h311a zt zcard centre h78 sec713Y L.corB L.outSolv L.twoRank
        borelRankOneSolvable_holds artinLinearOrders_holds
        radicalTwoSubgroupLinearStatement_holds)
  exact ⟨h78, h79,
    stroth716Type_of_inputs_root h78 h79 h711S h713 h714 h715 omegaSignStatement_holds hNR hZV
      hNL L.tim81unRoot (sec716NoLargeUnitaryRoot_of h78 zt zcard) hSub,
    stroth717_of_cases_root h78 hA inv717
      (step717NotUnitary_of_inputs h34 h311a h713 unitarySixLevi_holds L.outSolvU6) h711S
      h713 hNR hZV hNL L.tim81unRoot hSub⟩

end Assembly

end CFSG.RankThree.GF2n.Stroth80
