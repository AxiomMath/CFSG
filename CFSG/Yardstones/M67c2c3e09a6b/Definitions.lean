module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.Tables112Split
public import CFSG.HardMathSupport.Solomon.LocalBalance.Input1433Type
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma43Rest
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2Defs
public import CFSG.HardMathSupport.Solomon.Coordinator.I25_3Defs
public import CFSG.HardMathSupport.Solomon.Coordinator.I19_10Red
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporAssemble
public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3J4
public import CFSG.HardMathSupport.Solomon.Coordinator.B3LieRes
public import CFSG.HardMathSupport.Solomon.Coordinator.I27_1Fam
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input252

public section

namespace CFSG.Yardstones.M67c2c3e09a6b

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

structure KGroupTables : Prop where
  tables112Rest : CFSG.HardMathSupport.Timmesfeld.ComponentBalance.Tables112Rest
  kernelT : CFSG.HardMathSupport.Timmesfeld.ComponentBalance.KernelT

structure LocalThreeBalanceSimpleFamilies : Prop where
  crossChar : CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeBalanceCrossChar
  sporadic : CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeBalanceSporadic

structure LocalTwoBalanceThreeFive : Prop where
  crossCharThree : CFSG.HardMathSupport.Solomon.Coordinator.LocalTwoBalanceCrossCharThree
  sporadicThree : CFSG.HardMathSupport.Solomon.Coordinator.LocalTwoBalanceSporadicThree
  crossCharFive : CFSG.HardMathSupport.Solomon.Coordinator.LocalTwoBalanceCrossCharFive
  sporadicFive : CFSG.HardMathSupport.Solomon.Coordinator.LocalTwoBalanceSporadicFive

structure SporadicBpResiduals : Prop where
  j4Three : CFSG.HardMathSupport.Solomon.Coordinator.J4ThreeCentralizerResidual
  restPairs : ∀ (name : TauCeti.SporadicName) (p : ℕ),
    CFSG.HardMathSupport.Solomon.Coordinator.B3SporRestPair name p → p ≠ 3 →
      CFSG.HardMathSupport.Solomon.Coordinator.B3SporPair name p

structure LieCentralizerResiduals : Prop where
  semisimpleCent : CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimpleCent
  defCharOuter : CFSG.HardMathSupport.Solomon.Coordinator.LieDefCharOuter

structure PumpingUpFacts : Prop where
  input14_33 : CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.Input14_33TypeSameField
  input14_20_7 : CFSG.HardMathSupport.Solomon.LocalBalance.Input14_20_7
  gapFinalPumpup : CFSG.HardMathSupport.Solomon.Coordinator.GapFinalPumpup

structure PumpingUpConsumerFacts : Prop where
  input14_33 : CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.Input14_33
  input14_20_7 : CFSG.HardMathSupport.Solomon.LocalBalance.Input14_20_7
  gapFinalPumpup : CFSG.HardMathSupport.Solomon.Coordinator.GapFinalPumpup

structure LThreeFourComponentFacts : Prop where
  input25_3 : CFSG.HardMathSupport.Solomon.Coordinator.Input25_3FactsNo38
  input25_2 : CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input25_2FactsNarrow

structure I271OpenFamilies : Prop where
  nnHatSixRank : CFSG.HardMathSupport.Solomon.Coordinator.I271NNHatSixRank
  nnOther : CFSG.HardMathSupport.Solomon.Coordinator.I271NNOther
  altDiv : CFSG.HardMathSupport.Solomon.Coordinator.I271AltDiv
  altNdiv : CFSG.HardMathSupport.Solomon.Coordinator.I271AltNdiv
  chevPBal : CFSG.HardMathSupport.Solomon.Coordinator.I271ChevPBal
  chevPExc : CFSG.HardMathSupport.Solomon.Coordinator.I271ChevPExc
  sporGen : CFSG.HardMathSupport.Solomon.Coordinator.I271SporGen
  autBalanceON : CFSG.HardMathSupport.Solomon.Coordinator.I271AutBalanceON
  onLow : CFSG.HardMathSupport.Solomon.Coordinator.I271ONLow
  chevQL34 : CFSG.HardMathSupport.Solomon.Coordinator.I271ChevQLThreeFour
  chevQ : CFSG.HardMathSupport.Solomon.Coordinator.I271ChevQ

@[expose] def MovingAround : Prop :=
  Prop98 → TheoremTwo

end CFSG.Yardstones.M67c2c3e09a6b
