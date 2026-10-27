module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFinalChainInterface

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.LinearChain

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

variable {G : Type} [Group G]

@[expose] def TwoCoreInvolutionGrowthConclusion (H : Subgroup G) (z : G) : Prop :=
  let Q := minimalLocalFailurePairActionPointHull H z
  let M := TwoCoreGrowth.pointTwoCoreImage H
  Q < M →
    Q < Subgroup.closure {m : G | m ∈ M ∧ orderOf m = 2} ∧ ∃ m ∈ M, orderOf m = 2 ∧ m ∉ Q

@[expose] def RootCentralizerOddCoreFreeConclusion (H : Subgroup G) (z : G) : Prop :=
  let Q := minimalLocalFailurePairActionPointHull H z
  let C := H ⊓ Subgroup.centralizer (Q : Set G)
  ∃ _ : (Q.subgroupOf C).Normal, CFSG.oddCore (↥C ⧸ Q.subgroupOf C) = ⊥

@[expose] def TrivialPairTwoCoreConclusion (H : Subgroup G) (z : G) (beta : rightCosetSpace H)
    (t : G) : Prop :=
  let K := minimalLocalFailureProperPairHull H z beta t
  let Q := minimalLocalFailurePairActionPointHull H z
  let J := Subgroup.centralizer (K : Set G)
  let C := H ⊓ Subgroup.centralizer (Q : Set G)
  let M := TwoCoreGrowth.pointTwoCoreImage H
  CFSG.pCore 2 J = ⊥ →
    M = Q ∧ Subgroup.closure {m : G | m ∈ M ∧ orderOf m = 2} = Q ∧
      ∃ _ : (Q.subgroupOf C).Normal, CFSG.pCore 2 (↥C ⧸ Q.subgroupOf C) = ⊥

@[expose] def RootQuotientCharacterSetupConclusion (H : Subgroup G) (z : G)
    (beta : rightCosetSpace H) (t : G) : Prop :=
  let K := minimalLocalFailureProperPairHull H z beta t
  let Q := minimalLocalFailurePairActionPointHull H z
  let J := Subgroup.centralizer (K : Set G)
  let C := H ⊓ Subgroup.centralizer (Q : Set G)
  CFSG.pCore 2 J = ⊥ →
    ∃ _ : (Q.subgroupOf C).Normal,
      CFSG.pCore 2 (↥C ⧸ Q.subgroupOf C) = ⊥ ∧ CFSG.oddCore (↥C ⧸ Q.subgroupOf C) = ⊥ ∧
      ∀ u : C, (u : G) ∈ J → orderOf (u : G) = 2 →
        ∃ W : Subgroup G, W ≤ J ∧ IsCyclic W ∧ Odd (Nat.card W) ∧ 3 ≤ Nat.card W ∧
          let π := QuotientGroup.mk' (Q.subgroupOf C)
          let Wbar := (W.subgroupOf C).map π
          IsCyclic Wbar ∧ Nat.card Wbar = Nat.card W ∧ orderOf (π u) = 2 ∧ π u ∉ Wbar ∧
          (∀ w ∈ Wbar, (π u)⁻¹ * w * π u = w⁻¹) ∧
          (∀ W₀ : Subgroup (↥C ⧸ Q.subgroupOf C), W₀ ≤ Wbar → W₀ ≠ ⊥ →
            Subgroup.centralizer (W₀ : Set (↥C ⧸ Q.subgroupOf C)) = Wbar ∧
            Subgroup.normalizer (W₀ : Set (↥C ⧸ Q.subgroupOf C)) =
              Wbar ⊔ Subgroup.zpowers (π u)) ∧
          ∀ N : Subgroup (↥C ⧸ Q.subgroupOf C), N.Normal → N ≠ ⊥ → π u ∈ N

@[expose] def RootQuotientInvolutionClassesConclusion (H : Subgroup G) (z : G)
    (beta : rightCosetSpace H) : Prop :=
  let B := pairPointStabilizer H beta
  let Q := minimalLocalFailurePairActionPointHull H z
  let C := H ⊓ Subgroup.centralizer (Q : Set G)
  (∀ u ∈ B, orderOf u = 2 →
    Nat.card Q ∣ 2 ^ ((H ⊓ Subgroup.normalizer ((fun x => u * x) '' (Q : Set G))).relIndex
      H).factorization 2) ∧
  ∃ _ : (Q.subgroupOf C).Normal, ∃ a b : ↥C ⧸ Q.subgroupOf C,
    orderOf a = 2 ∧ orderOf b = 2 ∧ ¬ IsConj a b

@[expose] def PairCentralizerTwoCoreNontrivialConclusion (H : Subgroup G) (z : G)
    (beta : rightCosetSpace H) (t : G) : Prop :=
  CFSG.pCore 2 (Subgroup.centralizer (minimalLocalFailureProperPairHull H z beta t : Set G)) ≠ ⊥

@[expose] def NontrivialPairTwoCoreConclusion (H : Subgroup G) (z : G)
    (beta : rightCosetSpace H) (t : G) : Prop :=
  CFSG.pCore 2 (Subgroup.centralizer (minimalLocalFailureProperPairHull H z beta t : Set G)) ≠ ⊥ →
    FinalChain.RootCentralizerTwoCoreConclusion H z beta t

end CFSG.ShultStronglyClosedTI.LinearChain
