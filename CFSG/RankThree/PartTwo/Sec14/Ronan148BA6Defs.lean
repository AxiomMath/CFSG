module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec14.Item148HJResProofYd
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148B

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS Main148 HJRes148

@[expose] def Step148A6PointQ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A),
    letI := ker148_normal hY.2
    ∀ J ∈ thetaComponentsIn Y, A ≤ Subgroup.normalizer (J : Set G) →
      Sec4.IsTripleCover ↥(img148 A Y J) (alternatingGroup (Fin 6)) →
      img148 A Y (deltaZero A (lB A) Y) = img148 A Y J →
    ∀ K : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y), IsComponent K → K ≠ img148 A Y J →
      Sec4.IsTripleCover ↥K (alternatingGroup (Fin 6)) → K ≤ img148 A Y Y →
    ∀ k ∈ img148 A Y A, k ∈ K → k ∉ Subgroup.centralizer (K : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) →
      img148 A Y A ⊓ Subgroup.centralizer (K : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) ⊔
          Subgroup.zpowers k = img148 A Y A →
    ∀ (a : G) (ha : a ∈ A), Subgroup.zpowers a ∈ omegaA A →
      alpha148 A Y a ha ∈ Subgroup.centralizer (K : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) → False

end CFSG.RankThree.PartTwo.Sec14.Ronan148B
