module

public import CFSG.Open.FusionDefs
public import CFSG.Blueprint.Catalog
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.Open.RankThreeDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Blueprint (LieModel)

structure K335Hyp (G : Type) [Group G] [Finite G] (L P : Subgroup G) : Prop where
  kGroup : CFSG.Open.IsKGroup G
  rank : CFSG.Open.pRank 3 (⊤ : Subgroup G) ≤ 3
  lie : LieModel ↥L .PSL 3 2 2
  sylow : CFSG.ABGLocalTools.IsSylowOf 3 P L
  gamma : CFSG.Open.rankThreeGamma 1 3 P ≤ Subgroup.normalizer (L : Set G)
  closed : ∀ a ∈ P, ∀ g : G, g⁻¹ * a * g ∈ Subgroup.normalizer (P : Set G) → g⁻¹ * a * g ∈ P

structure K335MinCex (G : Type) [Group G] [Finite G] (L P : Subgroup G) : Prop where
  hyp : K335Hyp G L P
  ne_top : Subgroup.normalizer (L : Set G) ≠ ⊤
  min : ∀ (H : Type) [Group H] [Finite H], Nat.card H < Nat.card G →
    ∀ L' P' : Subgroup H, K335Hyp H L' P' → Subgroup.normalizer (L' : Set H) = ⊤

structure K335Quasi (G : Type) [Group G] [Finite G] (L P S : Subgroup G) : Prop where
  kGroup : CFSG.Open.IsKGroup G
  rank : CFSG.Open.pRank 3 (⊤ : Subgroup G) ≤ 3
  lie : LieModel ↥L .PSL 3 2 2
  sylowL : CFSG.ABGLocalTools.IsSylowOf 3 P L
  gamma : CFSG.Open.rankThreeGamma 1 3 P ≤ Subgroup.normalizer (L : Set G)
  ne_top : Subgroup.normalizer (L : Set G) ≠ ⊤
  elem : CFSG.Open.IsElemAbelian 3 P
  card : Nat.card P = 9
  sylow : CFSG.ABGLocalTools.IsSylowOf 3 S ⊤
  le : P ≤ S
  normal : S ≤ Subgroup.normalizer (P : Set G)
  closed : CFSG.Open.fusionStronglyClosed (P : Set G) S
  quasi : CFSG.Open.IsQuasisimple G
  center : IsPGroup 3 (Subgroup.center G)
  disjoint : P ⊓ Subgroup.center G = ⊥

structure K335StrongE9 {G : Type} [Group G] (P S : Subgroup G) : Prop where
  le : P ≤ S
  sylow : CFSG.ABGLocalTools.IsSylowOf 3 S ⊤
  elem : CFSG.Open.IsElemAbelian 3 P
  card : Nat.card P = 9
  closed : CFSG.Open.fusionStronglyClosed (P : Set G) S

@[expose] def K335NoStrongE9 (G : Type) [Group G] : Prop :=
  ∀ P S : Subgroup G, ¬ K335StrongE9 P S

theorem K335Quasi.strongE9 {G : Type} [Group G] [Finite G] {L P S : Subgroup G}
    (h : K335Quasi G L P S) : K335StrongE9 P S :=
  ⟨h.le, h.sylow, h.elem, h.card, h.closed⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
