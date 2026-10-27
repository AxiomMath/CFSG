module

public import CFSG.Blueprint.Catalog
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.Open.GeneralizedFittingSelfCentralizingMilestoneDefs
public import CFSG.Open.RankThreeDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Blueprint (LieModel)

@[expose] def K328 : Prop :=
  ∀ (G : Type) [Group G] [Finite G],
    CFSG.Open.IsQuasisimple ↥(CFSG.Open.genFittingFStar G) →
    CFSG.Open.IsKGroup (↥(CFSG.Open.genFittingFStar G) ⧸
      Subgroup.center ↥(CFSG.Open.genFittingFStar G)) →
    CFSG.Open.pRank 3 (⊤ : Subgroup G) ≤ 3 →
    ∀ Z X P : Subgroup G, Nat.card Z = 3 → Z ≤ X →
      X ≤ Subgroup.centralizer (Z : Set G) ⊓ CFSG.Open.genFittingFStar G →
      (X.subgroupOf (Subgroup.centralizer (Z : Set G) ⊓
        CFSG.Open.genFittingFStar G)).IsSubnormal →
      CFSG.Open.IsQuasisimple ↥X → Nat.card (Subgroup.center ↥X) = 3 →
      (LieModel (↥X ⧸ Subgroup.center ↥X) .PSL 3 2 2 ∨
        LieModel (↥X ⧸ Subgroup.center ↥X) .PSU 3 2 3) →
      CFSG.ABGLocalTools.IsSylowOf 3 P X → CFSG.Open.rankThreeGamma 1 3 P = ⊤

@[expose] def K329 : Prop :=
  ∀ (G : Type) [Group G] [Finite G],
    CFSG.Open.IsQuasisimple ↥(CFSG.Open.genFittingFStar G) →
    CFSG.Open.IsKGroup (↥(CFSG.Open.genFittingFStar G) ⧸
      Subgroup.center ↥(CFSG.Open.genFittingFStar G)) →
    CFSG.Open.pRank 3 (⊤ : Subgroup G) ≤ 3 →
    ∀ X P : Subgroup G, X ≤ CFSG.Open.genFittingFStar G → LieModel ↥X .PSU 3 2 3 →
      CFSG.ABGLocalTools.IsSylowOf 3 P X →
      CFSG.Open.rankThreeGamma 1 3 P ≤ Subgroup.normalizer (X : Set G) →
      X = CFSG.Open.genFittingFStar G

@[expose] def K335 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Open.IsKGroup G →
    CFSG.Open.pRank 3 (⊤ : Subgroup G) ≤ 3 →
    ∀ L P : Subgroup G, LieModel ↥L .PSL 3 2 2 → CFSG.ABGLocalTools.IsSylowOf 3 P L →
      CFSG.Open.rankThreeGamma 1 3 P ≤ Subgroup.normalizer (L : Set G) →
      (∀ a ∈ P, ∀ g : G, g⁻¹ * a * g ∈ Subgroup.normalizer (P : Set G) → g⁻¹ * a * g ∈ P) →
      Subgroup.normalizer (L : Set G) = ⊤

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
