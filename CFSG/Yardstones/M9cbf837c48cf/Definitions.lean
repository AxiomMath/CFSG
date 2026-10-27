module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Bal3Lemma2_1Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_10Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34KFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5KFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2Z_Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.SignalizerNoncentral2_7KFact
public import CFSG.LocalAnalysis.RankThreeUC.TheoremDResidual7
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Yardstones.M9cbf837c48cf

@[expose] def AGL81TheoremDSection15Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    CFSG.Open.IsKProper G → CFSG.Open.IsCharTwoType G → CFSG.Open.evenRank G = 3 →
      CFSG.LocalAnalysis.RankThreeUC.AGL81Residual7NoU4 G

@[expose] def AGL81TheoremDSection16Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    CFSG.Open.IsKProper G → CFSG.Open.IsCharTwoType G → CFSG.Open.evenRank G = 3 →
      CFSG.LocalAnalysis.RankThreeUC.AGL81Residual7U4 G

@[expose] def GL83GenericKFactsStatement : Prop :=
  CFSG.LocalAnalysis.RankThreeTheoremC.StronglyEmbeddedCyclicOuterKFact ∧
  CFSG.LocalAnalysis.RankThreeTheoremC.SignalizerTwoGroupKFact ∧
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactSignalizerTrivial ∧
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactWeakClosure ∧
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactInnerAction ∧
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactU3Involution ∧
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactComponentPCoreThree ∧
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactL34Unitary ∧
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactL34Borel ∧
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactL34Graph ∧
  CFSG.LocalAnalysis.RankThreeTheoremC.Bal3KFacts ∧
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactZJFactorization ∧
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactAlmostSimpleRankTwo

end CFSG.Yardstones.M9cbf837c48cf
