module

public import CFSG.HardMathSupport.Solomon.LocalBalance.InputUniqProof
public import CFSG.HardMathSupport.Solomon.Coordinator.PumpingUpFinal
public import CFSG.HardMathSupport.Dickson.Sec6.AssemblyRest
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Residual16Holds
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Assembly14
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.TriXMinus
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.TriXPlusAt

public section

namespace CFSG.Yardstones.M67c2c3e09a6b

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

theorem kGroupTables :
    KGroupTables :=
  have T := CFSG.HardMathSupport.Timmesfeld.Coordinator.tables112_holds
  ⟨⟨T.T1a, T.T1b, T.T2, T.T3, T.T11, T.T9, T.TFA_a, T.TFA_b⟩,
    CFSG.HardMathSupport.Timmesfeld.Coordinator.kernelT_of_kernel11_6T
      (CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.kernel11_6T_of_tables
        CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
        (CFSG.HardMathSupport.Timmesfeld.Coordinator.sporadicMultipliers_of_census
          CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds))⟩

theorem localThreeBalanceSimpleFamilies :
    LocalThreeBalanceSimpleFamilies :=
  ⟨CFSG.HardMathSupport.Timmesfeld.Coordinator.localThreeBalanceCrossChar_holds,
    CFSG.HardMathSupport.Timmesfeld.Coordinator.localThreeBalanceSporadic_holds⟩

theorem localTwoBalanceThreeFive :
    LocalTwoBalanceThreeFive :=
  have h := CFSG.HardMathSupport.Dickson.LocalTwoBalance.localTwoBalanceThreeFive_parts
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

theorem localTwoBalanceSimpleGtFive :
    CFSG.HardMathSupport.Timmesfeld.LocalTwo.LocalTwoBalanceSimpleGtFive :=
  CFSG.HardMathSupport.Timmesfeld.Coordinator.localTwoBalanceSimpleGtFive_holds

theorem sporadicBpResiduals :
    SporadicBpResiduals :=
  ⟨CFSG.HardMathSupport.Solomon.Coordinator.j4ThreeCentralizerResidual
      CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group,
    CFSG.HardMathSupport.Solomon.Coordinator.b3SporRestPairs_of
      (CFSG.HardMathSupport.Solomon.Coordinator.b3SporPair_B_seven
        CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
        CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds)⟩

theorem lieCentralizerResiduals :
    LieCentralizerResiduals :=
  ⟨CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.lieSemisimpleCent,
    CFSG.HardMathSupport.Dickson.DefCharOuter.lieDefCharOuter⟩

theorem pumpingUpFacts :
    PumpingUpFacts :=
  CFSG.HardMathSupport.Solomon.Coordinator.pumpingUpFacts_holds

theorem lThreeFourComponentFacts :
    LThreeFourComponentFacts :=
  CFSG.HardMathSupport.Solomon.Coordinator.YS08.lThreeFourComponentFacts_holds

theorem i271OpenFamilies :
    I271OpenFamilies :=
  CFSG.HardMathSupport.Dickson.Sec6.i271OpenFamilies_of_chevQ
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.i271ChevQ_holds

theorem th1J1Factorization :
    CFSG.HardMathSupport.Solomon.Coordinator.I28_8.Th1J1Factorization :=
  CFSG.HardMathSupport.Solomon.Coordinator.I28_8.th1J1Factorization

theorem inputUniq : CFSG.HardMathSupport.Solomon.LocalBalance.CaseThreeNs.InputUniq :=
  CFSG.HardMathSupport.Solomon.LocalBalance.CaseThreeNs.inputUniq_holds

theorem sec6Out :
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6Out :=
  CFSG.HardMathSupport.Dickson.Sec6.sec6Out_of_chevQ
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.i271ChevQ_holds

theorem prop95 :
    Prop95 :=
  CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.prop95_holds

theorem movingAround :
    MovingAround :=
  CFSG.LocalAnalysis.GLTheoremB.MovingAround.movingAround_of_inputs
    (CFSG.LocalAnalysis.GLTheoremB.MovingAround.TriXMinus.triXNoGCentUniPlanes_of_at_one
      CFSG.LocalAnalysis.GLTheoremB.MovingAround.TriXPlus.triXNoGCentUniPlanesAt_one)

end CFSG.Yardstones.M67c2c3e09a6b
