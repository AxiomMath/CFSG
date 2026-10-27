module

public import CFSG.RankThree.PartTwo.Sec14.Liebeck1418BridgeHolds
public import CFSG.RankThree.PartTwo.Sec14.Wales1418OffPoint
public import CFSG.RankThree.PartTwo.Sec14.Ronan148MAssembly
public import CFSG.RankThree.PartTwo.Sec14.Item1413Res5ProofPGL
public import CFSG.RankThree.PartTwo.Sec14.Ronan149Holds
public import CFSG.RankThree.PartTwo.Sec4.Wales430
public import CFSG.RankThree.PartTwo.Sec4.Wales430Theta
public import CFSG.RankThree.PartTwo.Sec4.Statements430L3
public import CFSG.RankThree.PartTwo.Sec4.Statements417
public import CFSG.RankThree.PartTwo.Sec4.Item417Res6Proof
public import CFSG.RankThree.PartTwo.Sec4.Item45Closed
public import CFSG.RankThree.PartTwo.Sec4.StatementsComponents
public import CFSG.RankThree.PartTwo.Sec4.Item41NarrowGriess
public import CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest
public import CFSG.RankThree.PartTwo.Sec4.T444.DiagGriess
public import CFSG.RankThree.PartTwo.Sec4.Item413CoverProofClose47
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.I417J3
public import CFSG.RankThree.PartTwo.Sec4.Item424Res7ProofG23
public import CFSG.RankThree.PartTwo.Sec4.Item417Res7ProofG2Odd
public import CFSG.RankThree.PartTwo.Sec4.Item417Res7ProofD4Odd
public import CFSG.RankThree.PartTwo.Sec4.Item417Res7ProofG2
public import CFSG.RankThree.PartTwo.Sec4.Item417Res8ProofD4Even
public import CFSG.RankThree.PartTwo.Sec21.ReeF4Conj2Proof
public import CFSG.RankThree.PartTwo.Sec4.Item417Res7ProofTits
public import CFSG.RankThree.PartTwo.Sec4.Item417Res5ProofMcL
public import CFSG.RankThree.PartTwo.Sec4.Item417Res5ProofG23
public import CFSG.RankThree.PartTwo.KFacts.KFOut3Holds
public import CFSG.RankThree.PartTwo.KFacts.KF430LiePG2
public import CFSG.RankThree.PartTwo.KFacts.KF430LiePSU
public import CFSG.RankThree.PartTwo.KFacts.KF430ONProof
public import CFSG.RankThree.PartTwo.KFacts.KF1418MJProof
public import CFSG.RankThree.PartTwo.Sec11.Item11CloseNarrow
public import CFSG.HardMathSupport.Seitz.G2Noninner.Descent.OddNeThree
public import CFSG.HardMathSupport.Seitz.G2Noninner.SubfieldPair.Final
public import CFSG.LieType.SeitzGeneration.ExcOuterAssemblyV5
public import CFSG.LieType.SeitzGeneration.OmegaF2.Basic
public import CFSG.LieType.SeitzGeneration.RootPairOrthBlock
public import CFSG.LieType.SeitzGeneration.RootPairSp
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSeitzCyc
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsBorLie
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsThree
public import CFSG.RankThree.PartTwo.Sec14.Item1411StepsProof
public import CFSG.RankThree.PartTwo.Sec14.Item1413Proof1417
public import CFSG.RankThree.PartTwo.Sec14.Item1413ProofFrame
public import CFSG.RankThree.PartTwo.Sec14.Item1413ProofRoute
public import CFSG.RankThree.PartTwo.Sec14.Item1413Res3ProofDefs
public import CFSG.RankThree.PartTwo.Sec14.Item1418Res2ProofDefs
public import CFSG.RankThree.PartTwo.Sec21.Item223RankResProofAut
public import CFSG.RankThree.PartTwo.Sec4.Item413Back
public import CFSG.RankThree.PartTwo.Sec4.Item413J3
public import CFSG.RankThree.PartTwo.Sec4.Item413Native
public import CFSG.RankThree.PartTwo.Sec4.Item4Res3ProofInputs

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13

theorem step1418OffLayerR_of_step430L3
    (hL3 : Sec4.Step430L3) : Step1418OffLayerR := by
  obtain ⟨h45, -, h41, h422, h46, -, -, h131, -, -, h142⟩ := Ronan148M.closedInputs
  have hPGL : Item1412NotPGLR := item1412NotPGLR_of h131 h142 Ronan149.item145BotS14_holds
  have h430 : Sec4.Item4_30 := Sec4.Proof430.item4_30_of (Sec4.item4_17_of_res6Narrow
      Sec4.rank3II_4_5 (Sec4.rank3II_4_7_of_46 (Sec4.Census.rank3II_4_6_of_griess_noItem41
          ComponentClassification.TBLit.griessMultipliersAllModels_holds
          (Sec4.Census.coverCenterThreeRest_of
              ComponentClassification.TBLit.griessMultipliersAllModels_holds))) Sec4.diag_item43_holds
      (Sec4.Census.rank3II_4_6_of_griess_noItem41
          ComponentClassification.TBLit.griessMultipliersAllModels_holds
          (Sec4.Census.coverCenterThreeRest_of
              ComponentClassification.TBLit.griessMultipliersAllModels_holds)) CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
      CFSG.AGLEmbeddingD2.Wilson.NormalizerAction.item417InJ3Rest_holds
      Sec4.Res417Five.TorusSep.k417G2CoverCent_holds Sec4.Res417Seven.k417G2OddCentSU3_holds
      Sec4.Res417Seven.k417NoDatumD4Odd_holds Sec4.Res417Seven.k417DatumG2Even_holds
      Sec4.Res417Eight.k417DatumD4Even_holds Sec8.reeF4OrderThreeConj_holds
      Sec4.Res417Seven.k417TitsCentThree_holds Sec4.Res417Five.k417E81McL_holds
      Sec4.Res417Five.k417E81G23_holds) h45
    (KFacts.KF430.kf430LieP_of_parts KFacts.KF430.kf430LiePG2_holds KFacts.KF430.kf430LiePSp_holds
        KFacts.KF430.kf430LiePSU_holds KFacts.KF430.kf430LiePSL_holds) KFacts.KF430ONProof.kf430ON_holds hL3
  exact Liebeck1418Bridge.step1418OffLayerR_of_point
    (step1418OffPointR_of h422 h45 h46 h131 hPGL (Sec4.item4_30Theta_of h430 h41)
      Sec11.item1134E27_of_standing_narrow KFacts.kfOut3_holds
      KFacts.KF1418MJProof.kf1418MJ_holds)

end CFSG.RankThree.PartTwo.Sec14
