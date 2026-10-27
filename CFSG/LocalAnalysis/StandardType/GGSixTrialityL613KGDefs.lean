module

public import CFSG.LocalAnalysis.StandardType.GGSixTrialityL613Defs
public import CFSG.LocalAnalysis.StandardType.GGHypSixD4RankTransfer

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin CFSG.StandardType.Triality
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.PartOne.AUTSL
  CFSG.ComponentClassification.OuterAutomorphisms

section Matrix

@[expose] def GGD4OuterSylowInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 3 ∣ Nat.card K - 1 →
    ∀ α : MulAut (Om8 K), α ^ 3 = 1 → ∀ S : Sylow 3 (Om8 K),
      (∀ s ∈ (S : Subgroup (Om8 K)), α s = s) → α ∈ inner (Om8 K)

@[expose] def GGD4SemilinearLayerInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (f : ℕ), Nat.card K = 2 ^ f →
    ∀ α : MulAut (Om8 K), α ^ 3 = 1 → α ∉ inner (Om8 K) →
      (∃ g : similarityPairs (coordinateQuadPlus 4 K), conjAct _ g = α) →
      ∀ X : Subgroup (Om8 K), (∀ x ∈ X, α x = x) → ⁅X, X⁆ = X →
        ¬ LieModel (↥X ⧸ Subgroup.center ↥X) .PSL 3 2 f

@[expose] def GGD4CentralClassThreeInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 3 ∣ Nat.card K - 1 →
    ∀ z : Om8 K, z ^ 3 = 1 → z ≠ 1 → ¬ 3 ∣ (Subgroup.centralizer {z}).index →
      ∀ α : MulAut (Om8 K), α ^ 3 = 1 →
        (∀ g : similarityPairs (coordinateQuadPlus 4 K), conjAct _ g ≠ α) → α z = z →
          D4Rank.omFixDim z = 2

@[expose] def GGD4ClassThreeLayerInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 3 ∣ Nat.card K - 1 →
    ∀ z : Om8 K, z ^ 3 = 1 → D4Rank.omFixDim z = 2 →
      ∃ S : Subgroup (Om8 K), ⁅S, S⁆ = S ∧ z ∈ S ∧ S ≤ Subgroup.centralizer {z} ∧
        (∀ X : Subgroup (Om8 K), X ≤ Subgroup.centralizer {z} → ⁅X, X⁆ = X → X ≤ S) ∧
        Nat.card S ≤ 3 * Nat.card (StatedProj (StatedSL 3 K))

@[expose] def GGD4ClassThreeCentralInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 3 ∣ Nat.card K - 1 →
    ∀ z : Om8 K, z ^ 3 = 1 → D4Rank.omFixDim z = 2 →
      ¬ 3 ∣ (Subgroup.centralizer {z}).index ∧ ∀ α : MulAut (Om8 K), ∃ g : Om8 K, α z = g * z * g⁻¹

end Matrix

section Config

@[expose] def GGSixTrialityDClassThreeInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) (f : ℕ)
    (ψ : (ggU .POmegaPlus 4 f).K →* G),
    GGSixCtxV2 3 B Bs x L D J (ggU .POmegaPlus 4 f).D .POmegaPlus 4 f ψ →
    Subgroup.centralizer (ggG0 3 B x L D J : Set G) = ⊥ →
    ∀ y ∈ ggM 3 B x L D J, orderOf y = 3 →
      GGSixTrialityCase 3 B x L D J (ggU .POmegaPlus 4 f).D .POmegaPlus 4 f ψ y →
        ∃ d ∈ D, d ≠ 1 ∧ ∃ u : Sp8 (GaloisField 2 f), ψ u = d ∧ D4Rank.omFixDim (model8 u) = 2

end Config

end CFSG.StandardType
