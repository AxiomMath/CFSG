module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1KlingenIdent
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28PartsS
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Residues
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Lemma43A6
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1Red
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_10Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62wResDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2KFactLeavesCoreF
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2HSFiveCaseTwo3
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairStrong3KFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairRes3KFact
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairA6Ctx
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.StrongThreeAutomizer
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFInputs
public import CFSG.LocalAnalysis.RankThreeTheoremC.SignalizerNoncentral2_7KFact
public import CFSG.LocalAnalysis.RankThreeTheoremC.Bal3Lemma2_1Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2Z_Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank632Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank65Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank620Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank621Defs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.Yardstones.Mdac756b924db

open CFSG.LocalAnalysis

@[expose] def AGL81TheoremAResiduesE3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], RankThreeTheoremC.Setting G →
    RankThreeTheoremC.D1FrontierResidues3L G

@[expose] def GL83GenericL28ResiduesE3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], RankThreeTheoremC.Setting G →
    RankThreeTheoremC.TheoremD1 G → RankThreeTheoremC.FullCoreLocal G →
    RankThreeTheoremC.GL83GenericPrimeThreeL28Lemma43S G ∧
      RankThreeTheoremC.GL83Generic4_9BNonabS G

@[expose] def GL83GenericU3Lemma43E3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], RankThreeTheoremC.Setting G →
    RankThreeTheoremC.TheoremD1 G → RankThreeTheoremC.FullCoreLocal G →
    RankThreeTheoremC.GL83GenericPrimeThreeU3Lemma43 G

@[expose] def GL83GenericA6Lemma43E3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], RankThreeTheoremC.Setting G →
    RankThreeTheoremC.TheoremD1 G → RankThreeTheoremC.FullCoreLocal G →
    RankThreeTheoremC.GL83GenericPrimeThreeA6Lemma43VI G

@[expose] def GL83GenericL34RemarkE3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], RankThreeTheoremC.Setting G →
    RankThreeTheoremC.TheoremD1 G → RankThreeTheoremC.FullCoreLocal G →
    RankThreeTheoremC.GL83GenericPrimeThreeL34Remark G

@[expose] def GL83GenericListSporE3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], RankThreeTheoremC.Setting G →
    RankThreeTheoremC.TheoremD1 G → RankThreeTheoremC.FullCoreLocal G →
    RankThreeTheoremC.GL83GenericListExclusionRedSpor G

@[expose] def GL83GenericU3PlaneE3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], RankThreeTheoremC.Setting G →
    RankThreeTheoremC.TheoremD1 G → RankThreeTheoremC.FullCoreLocal G →
    RankThreeTheoremC.GL83GenericU3Plane G

@[expose] def GL83SmallRankProp622E3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], RankThreeTheoremC.Setting G →
    RankThreeTheoremC.TheoremD1 G → RankThreeTheoremC.TheoremD2 G →
    RankThreeTheoremC.FullCoreLocal G → RankThreeTheoremC.GL83SmallRankProp622 G

@[expose] def GL83SmallRankInterfaceE3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], RankThreeTheoremC.Setting G →
    RankThreeTheoremC.TheoremD1 G → RankThreeTheoremC.TheoremD2 G →
    RankThreeTheoremC.FullCoreLocal G → RankThreeTheoremC.GL83SmallRankInterfaceW G

@[expose] def GL83SmallRankLemma630E3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], RankThreeTheoremC.Setting G →
    RankThreeTheoremC.TheoremD1 G → RankThreeTheoremC.TheoremD2 G →
    RankThreeTheoremC.FullCoreLocal G → RankThreeTheoremC.GL83SmallRankLemma630Res G

structure AGL81TheoremAKFacts : Prop where
  p1LieOffChar : CFSG.AGLEmbedding.P1ThreeLieOffChar
  klingenSylow : RankThreeTheoremC.KFactKlingenSylowNormalCyclic
  blockAltNormalizer : CFSG.AGLEmbedding.CitedBlockAltNormalizer
  gl83 : CFSG.RankThree.PartTwo.Sec21.GL83StronglyEmbeddedThreeSolvable
  sp62Frame : RankThreeTheoremC.KFactSp62Frame
  omega8Frame : RankThreeTheoremC.KFactOmega8Frame
  blockL28Rank : RankThreeTheoremC.KFactBlockL28Rank
  blockL28TwoRank : RankThreeTheoremC.KFactBlockL28TwoRank
  blockPerfectCoreThree : RankThreeTheoremC.KFactBlockPerfectCoreThree
  blockSylowThreeAut : RankThreeTheoremC.KFactBlockSylowThreeAut
  blockHeisenbergAut : RankThreeTheoremC.KFactBlockHeisenbergAut
  klingenLocal : RankThreeTheoremC.KFactKlingenLocal
  klingenThreeLocal : RankThreeTheoremC.KFactKlingenThreeLocal
  klingenFiveLocal : RankThreeTheoremC.KFactKlingenFiveLocal
  blockHeisenbergInner : RankThreeTheoremC.KFactBlockHeisenbergInner
  klingenIdent : RankThreeTheoremC.KFactKlingenIdent
  blockFieldIndex : RankThreeTheoremC.KFactBlockFieldIndex

structure AGL81TheoremBKFacts : Prop where
  d2 : RankThreeTheoremC.D2KFactLeavesCoreF
  blockRankOneOut : RankThreeTheoremC.KFactBlockRankOneOut
  blockOuterThree : RankThreeTheoremC.KFactBlockOuterThree
  blockE9Transitive : RankThreeTheoremC.KFactBlockE9Transitive
  blockPLElem : RankThreeTheoremC.KFactBlockPLElem
  sylowThreeAbelian : RankThreeTheoremC.KFactSylowThreeAbelian
  glaubermanNiles : CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNilesInput
  strongThreeAutomizer : CFSG.AGLEmbeddingD2.McLaughlin.KFactStrongThreeAutomizer
  blockOneImageIrr : RankThreeTheoremC.KFactBlockOneImageIrr3
  ffModule : CFSG.HardMathSupport.Cooperstein.Coordinator.FFModuleTheorem

structure GL83GenericKFacts : Prop where
  seCyclicOuter : RankThreeTheoremC.StronglyEmbeddedCyclicOuterKFact
  signalizerTwoGroup : RankThreeTheoremC.SignalizerTwoGroupKFact
  bal3 : RankThreeTheoremC.Bal3KFacts
  zjFactorization : RankThreeTheoremC.KFactZJFactorization
  almostSimpleRankTwo : RankThreeTheoremC.KFactAlmostSimpleRankTwo
  componentPCoreThree : RankThreeTheoremC.KFactComponentPCoreThree
  signalizerTrivial : RankThreeTheoremC.KFactSignalizerTrivial
  weakClosure : RankThreeTheoremC.KFactWeakClosure
  innerAction : RankThreeTheoremC.KFactInnerAction
  u3Involution : RankThreeTheoremC.KFactU3Involution
  l34Unitary : RankThreeTheoremC.KFactL34Unitary
  l34Borel : RankThreeTheoremC.KFactL34Borel
  l34Graph : RankThreeTheoremC.KFactL34Graph

structure GL83SmallRankKFacts : Prop where
  smallRankConstraint : RankThreeTheoremC.SmallRankConstraintKFact3
  sylowNormalizerIrreducible : RankThreeTheoremC.KFactSylowNormalizerIrreducible
  abelianSylowRankThree : RankThreeTheoremC.KFactAbelianSylowRankThree
  zAction628 : RankThreeTheoremC.KFactZAction628
  zAction629 : RankThreeTheoremC.KFactZAction629
  outThreePrimeSimple : RankThreeTheoremC.KFactOutThreePrimeSimple
  rankTwoUniqueness : RankThreeTheoremC.KFactRankTwoUniqueness
  rankThreeStructure : RankThreeTheoremC.KFactRankThreeStructure
  campbell : RankThreeTheoremC.KFactCampbell
  lemma2813 : RankThreeTheoremC.KFactLemma2813

end CFSG.Yardstones.Mdac756b924db
