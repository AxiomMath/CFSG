module

public import CFSG.RankThree.PartTwo.KFacts.K426RestON
public import CFSG.RankThree.PartTwo.KFacts.KSListsProof1118
public import CFSG.RankThree.PartTwo.KFacts.KSListsProof1121
public import CFSG.RankThree.PartTwo.Sec10.Item1012Res3ProofThree
public import CFSG.RankThree.PartTwo.Sec10.Item1012Res4ProofAut
public import CFSG.RankThree.PartTwo.Sec10.Item1012Res4ProofGL34
public import CFSG.RankThree.PartTwo.Sec10.Item1012ResProofKM3
public import CFSG.RankThree.PartTwo.Sec10.Item107Proof
public import CFSG.RankThree.PartTwo.Sec10.Item41ScopeProof
public import CFSG.RankThree.PartTwo.Sec10.Step1012ClaimProof
public import CFSG.RankThree.PartTwo.Sec10.Step1012ClaimKProofON
public import CFSG.RankThree.PartTwo.Sec11.AutThree1129.Assembly
public import CFSG.RankThree.PartTwo.Sec11.AutThree1129.D4
public import CFSG.RankThree.PartTwo.Sec11.Item1133Proof
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie2ProofBound
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie3ProofBound
public import CFSG.RankThree.PartTwo.Sec11.KS11LieProofND
public import CFSG.RankThree.PartTwo.Sec11.RonanD4Odd
public import CFSG.RankThree.PartTwo.Sec4.Item426RestProof
public import CFSG.RankThree.PartTwo.Sec4.Item48Proof
public import CFSG.RankThree.PartTwo.Sec4.RonanK423Items
public import CFSG.RankThree.PartTwo.Sec4.T444.DiagGriess
public import CFSG.RankThree.PartTwo.Sec8.Item82OneProof
public import CFSG.RankThree.PartTwo.Sec8.Item8ModelProofL3
public import CFSG.RankThree.PartTwo.Sec8.Item8ModelProofOddSL3
public import CFSG.RankThree.PartTwo.Sec9.Item95K
public import CFSG.RankThree.PartTwo.Sec9.Item98Proof
public import CFSG.RankThree.PartTwo.Sec9.NotLTwoEight

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Certified

namespace Close

theorem closed_sec4Item4_5
    : Sec4.Item4_5 :=
  Sec4.rank3II_4_5

theorem closed_sec4Item4_6
    : Sec4.Item4_6 :=
  Sec4.Census.rank3II_4_6_of_griess_noItem41
      ComponentClassification.TBLit.griessMultipliersAllModels_holds
      (Sec4.Census.coverCenterThreeRest_of
          ComponentClassification.TBLit.griessMultipliersAllModels_holds)

theorem closed_sec8KF82E9GTwo
    : Sec8.KF82E9GTwo :=
  Sec8.kF82E9GTwo_holds

theorem closed_sec8KF82E9PGUThree
    : Sec8.KF82E9PGUThree :=
  Sec8.kF82E9PGUThree_holds

theorem closed_sec8KF82E9ReeF4
    : Sec8.KF82E9ReeF4 :=
  Sec8.kF82E9ReeF4_holds

theorem closed_sec8KF82D4LangCoset
    : Sec8.KF82D4LangCoset :=
  Sec8.kF82D4LangCoset_holds

theorem closed_sec8KF82E9TrialityD4
    : Sec8.KF82E9TrialityD4 :=
  Sec8.kF82E9TrialityD4_of_lang closed_sec8KF82D4LangCoset

theorem closed_sec8KF82LThreeWrong
    : Sec8.KF82LThreeWrong :=
  Sec8.kF82LThreeWrong_holds

theorem closed_sec8KF82OddSLThree
    : Sec8.KF82OddSLThree :=
  Sec8.kF82OddSLThree_holds

theorem closed_sec8Item82One
    : Sec8.Item82One :=
  Sec8.item82One_of_item47W closed_sec4Item4_5 (Sec4.rank3II_4_7W_of closed_sec4Item4_6)
      closed_sec8KF82E9GTwo closed_sec8KF82E9PGUThree closed_sec8KF82E9ReeF4
      closed_sec8KF82E9TrialityD4 closed_sec8KF82LThreeWrong closed_sec8KF82OddSLThree

theorem closed_sec4Item4_8
    : Sec4.Item4_8 :=
  Sec4.rank3II_4_8_of closed_sec4Item4_5

theorem closed_sec9Item95
    : Sec9.Item95 :=
  Sec9.item95_of_item45 closed_sec4Item4_5 closed_sec4Item4_8

theorem closed_sec9NotLTwoEight
    : Sec9.NotLTwoEight :=
  Sec9.notLTwoEight_of closed_sec4Item4_5

theorem closed_sec9Item96
    : Sec9.Item96 :=
  Sec9.item96_of_item95 closed_sec8Item82One closed_sec9Item95 closed_sec4Item4_5
    closed_sec9NotLTwoEight

theorem closed_sec9Item97
    : Sec9.Item97 :=
  Sec9.item97_of_item48 closed_sec8Item82One closed_sec4Item4_5 closed_sec4Item4_8

theorem closed_sec9Item98
    : Sec9.Item98 :=
  Sec9.item98_of closed_sec4Item4_5 closed_sec9Item96

theorem closed_sec10Item107
    : Sec10.Item107 :=
  Sec10.item107_of closed_sec4Item4_5 closed_sec9Item97 closed_sec9Item98

theorem closed_sec4Item4_62
    : Sec4.Item4_62 :=
  Sec4.item4_62_holds

theorem closed_sec4Inputs47NoD4
    : Sec4.Inputs47NoD4 :=
  Sec4.inputs47NoD4

theorem closed_sec4Item4_7W
    : Sec4.Item4_7W :=
  Sec4.rank3II_4_7W_of_noD4 closed_sec4Item4_6 closed_sec4Inputs47NoD4

theorem closed_k426RestONThreeCentralizer
    : KFacts.K426Rest.ONThreeCentralizer :=
  KFacts.K426Rest.onThreeCentralizer

theorem closed_sec4Item4_26Theta
    : Sec4.Item4_26Theta :=
  Sec4.Item426Rest.item4_26Theta_of closed_sec4Item4_6 closed_sec4Item4_7W
    closed_k426RestONThreeCentralizer

theorem closed_tBLitGriessMultipliersAllModels
    :
    CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels :=
  CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds

theorem closed_sec4Item4_1LargePrime
    : Sec4.Item4_1LargePrime :=
  Sec4.Item41Narrow.item4_1LargePrime_of_griess closed_tBLitGriessMultipliersAllModels

theorem closed_sec4Item4_1ThreeCover
    : Sec4.Item4_1ThreeCover :=
  Sec4.Item41Narrow.item4_1ThreeCover_of_griess closed_tBLitGriessMultipliersAllModels

theorem closed_sec4Item4_3
    : Sec4.Item4_3 :=
  Sec4.diag_item43_holds

theorem closed_sec4Item4_9
    : Sec4.Item4_9 :=
  Sec4.rank3II_4_9

theorem closed_sec4Item4_23
    : Sec4.Item4_23 :=
  Sec4.item4_23_holds

theorem closed_sec10Item463Inv
    : Sec10.Item463Inv :=
  Sec4.RonanStep462.item463Inv_of_items_noAlt closed_sec4Item4_5 closed_sec4Item4_1LargePrime
    closed_sec4Item4_1ThreeCover closed_sec4Item4_3 closed_sec4Item4_9 closed_sec4Item4_7W
    closed_sec4Item4_23

theorem closed_sec10KS1012GL34
    : Sec10.KS1012GL34 :=
  Sec10.ks1012GL34_holds

theorem closed_sec10KS1012AutHyp
    : Sec10.KS1012AutHyp :=
  Sec10.ks1012AutHyp_holds

theorem closed_sec10Step1012ClaimKM3
    : Sec10.Step1012ClaimKM3 :=
  Sec10.step1012ClaimKM3_holds

theorem closed_sec10KS1012CoverThree
    : Sec10.KS1012CoverThree :=
  Sec10.Item1012Res3Proof.ks1012CoverThree_holds

theorem closed_sec10Step1012KAutSolv
    : Sec10.Step1012KAutSolv :=
  Sec10.SuzukiSectionProof.step1012KAutSolv_holds

theorem closed_sec10Step1012ClaimKd
    : Sec10.Step1012ClaimKd :=
  Sec10.step1012ClaimKd_of_solv closed_sec10KS1012CoverThree closed_sec10Step1012KAutSolv

theorem closed_sec10Step1012SClaim
    : Sec10.Step1012SClaim :=
  Sec10.step1012SClaim_of closed_sec4Item4_8 closed_sec10KS1012GL34 closed_sec10KS1012AutHyp
      (Sec10.step1012ClaimK_of closed_sec10Step1012ClaimKM3 closed_sec10Step1012ClaimKd)
      Sec10.step1012ClaimON_of

theorem closed_sec10Sec10X
    : Sec10.Sec10X :=
  Sec10.sec10X_of_claim closed_sec4Item4_5 closed_sec9Item97 closed_sec10Item107 closed_sec4Item4_62
    closed_sec4Item4_26Theta closed_sec10Item463Inv closed_sec10Step1012SClaim

theorem closed_sec10Sec10Never
    : Sec10.Sec10Never :=
  Sec10.sec10Never_of_sec10X closed_sec4Item4_5 closed_sec9Item97 closed_sec10Sec10X

theorem closed_sec10Item1016
    : Sec10.Item1016 :=
  Sec10.item1016_of_item96 closed_sec9Item96 closed_sec10Sec10Never

theorem closed_sec11NoOuterType424D4Odd
    : Sec11.NoOuterType424D4Odd :=
  Sec11.noOuterType424D4Odd_holds

theorem closed_sec11AutThree1129
    : Sec11.AutThree1129 :=
  AutThree1129.autThree1129_of_d4 (AutThree1129.autThreeAut_d4 closed_sec11NoOuterType424D4Odd)

theorem closed_sec11NoOuterType424G2Eight
    : Sec11.NoOuterType424G2Eight :=
  Sec11.noOuterType424G2Eight_holds

theorem closed_sec11ThetaCentral119G2Ss
    : Sec11.ThetaCentral119G2Ss :=
  Sec11.KS11Lie7Proof.thetaCentral119G2Ss_holds

theorem closed_sec11ThetaCentral119G2
    : Sec11.ThetaCentral119G2 :=
  Sec11.thetaCentral119G2_of_ss closed_sec11ThetaCentral119G2Ss

theorem closed_sec11CentJ119G2Inn
    : Sec11.CentJ119G2Inn :=
  Sec11.KS11Lie7Proof.centJ119G2Inn_holds

theorem closed_sec11CentJ119G2Out
    : Sec11.CentJ119G2Out :=
  Sec11.KS11Lie7Proof.centJ119G2Out_holds

theorem closed_sec11CentJ119G2
    : Sec11.CentJ119G2 :=
  Sec11.centJ119G2_of_parts closed_sec11CentJ119G2Inn closed_sec11CentJ119G2Out

theorem closed_thm1D4CocycleNF
    : CFSG.GH74.GLS.Stage2.Bender.Thm1.D4CocycleNF :=
  CFSG.GH74.GLS.Stage2.Bender.Thm1.d4CocycleNF_holds

theorem closed_sec11D4OuterStdNoType424
    : Sec11.D4OuterStdNoType424 :=
  Sec11.d4OuterStdNoType424_holds

theorem closed_sec11NoOuterType424D4Three
    : Sec11.NoOuterType424D4Three :=
  Sec11.noOuterType424D4Three_holds

theorem closed_sec11NoOuterType424D4
    : Sec11.NoOuterType424D4 :=
  Sec11.noOuterType424D4_of_parts closed_thm1D4CocycleNF closed_sec11D4OuterStdNoType424
    closed_sec11NoOuterType424D4Three

theorem closed_sec11ThetaCentral119D4Ss
    : Sec11.ThetaCentral119D4Ss :=
  Sec11.KS11Lie6Proof.thetaCentral119D4Ss_holds

theorem closed_sec11ThetaCentral119D4
    : Sec11.ThetaCentral119D4 :=
  Sec11.thetaCentral119D4_of_ss closed_sec11ThetaCentral119D4Ss

theorem closed_sec11CentJ119D4Inn
    : Sec11.CentJ119D4Inn :=
  Sec11.KS11Lie6Proof.centJ119D4Inn_holds

theorem closed_sec11CentJ119D4Out
    : Sec11.CentJ119D4Out :=
  Sec11.KS11Lie6Proof.centJ119D4Out_holds

theorem closed_sec11CentJ119D4
    : Sec11.CentJ119D4 :=
  Sec11.centJ119D4_of_parts closed_sec11CentJ119D4Inn closed_sec11CentJ119D4Out

theorem closed_sec11CentBound119
    : Sec11.CentBound119 :=
  Sec11.centBound119_of_eight closed_sec11NoOuterType424G2Eight closed_sec11ThetaCentral119G2
    closed_sec11CentJ119G2 closed_sec11NoOuterType424D4 closed_sec11ThetaCentral119D4
    closed_sec11CentJ119D4

theorem closed_sec11Item112
    : Sec11.Item112 :=
  Sec11.item112_of closed_sec9Item97 closed_sec9Item98 closed_sec4Item4_5 closed_sec4Item4_8

theorem closed_sec11Item111First
    : Sec11.Item111First :=
  Sec11.item111First_of closed_sec4Item4_5 closed_sec4Item4_8

theorem closed_sec11Item113
    : Sec11.Item113 :=
  Sec11.item113_of_item111First closed_sec9Item97 closed_sec11Item112 closed_sec4Item4_5
    closed_sec11Item111First

theorem closed_sec11Item1133
    : Sec11.Item1133 :=
  Sec11.item1133

theorem closed_sec11Item114
    : Sec11.Item114 :=
  Sec11.item114_of closed_sec11Item113

theorem closed_sec11NormCentJ1117G2Ss
    : Sec11.NormCentJ1117G2Ss :=
  Sec11.KS11Lie7Proof.normCentJ1117G2Ss_holds

theorem closed_sec11NormCentJ1117D4Ss
    : Sec11.NormCentJ1117D4Ss :=
  Sec11.KS11Lie6Proof.normCentJ1117D4Ss_holds

theorem closed_sec11KFact1117CubeG2
    : Sec11.KFact1117CubeG2 :=
  Sec11.kFact1117CubeG2_of_ss closed_sec11NormCentJ1117G2Ss closed_sec11NormCentJ1117D4Ss

theorem closed_sec11KFact1117CubeL3
    : Sec11.KFact1117CubeL3 :=
  Sec11.KS11LieProof.kFact1117CubeL3

theorem closed_sec11KFact1118Triality46
    : Sec11.KFact1118Triality46 :=
  Sec11.kFact1118Triality46

theorem closed_sec11KFact1121Lists
    : Sec11.KFact1121Lists :=
  Sec11.kFact1121Lists

theorem closed_sec11SetUp11
    : Sec11.SetUp11 :=
  Sec11.setUp11_of closed_sec9Item97 closed_sec4Item4_5 closed_sec4Item4_8

end Close

end Certified

end CFSG.RankThree.PartTwo.Sec11
