module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixElevenDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Preds

variable {G : Type} [Group G]

@[expose] def GGPCentralIn (p : ℕ) (M : Subgroup G) (z : G) : Prop :=
  z ∈ M ∧ ¬ p ∣ (Subgroup.centralizer {z}).relIndex M

end Preds

section Inputs

@[expose] def GGD4TrialityCentralInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (G₀ : Subgroup G) (t : StatedLieTag) (n f : ℕ)
    (ψ : (ggU t n f).K →* G),
    GGPresentsG0 G₀ (ggU t n f).D t n f ψ → Subgroup.centralizer (G₀ : Set G) = ⊥ →
    ∀ y ∈ Subgroup.normalizer (G₀ : Set G), orderOf y = 3 →
      GGTrialityCaseAt 3 G₀ (ggU t n f).D t n f ψ y →
    ∀ z : G, orderOf z = 3 → GGPCentralIn 3 (Subgroup.normalizer (G₀ : Set G)) z →
      z ∈ LargeEvenLayer (Subgroup.normalizer (G₀ : Set G) ⊓ Subgroup.centralizer {z}) ∧
        (∀ X : Subgroup G, X ≤ Subgroup.normalizer (G₀ : Set G) ⊓ Subgroup.centralizer {z} →
          ⁅X, X⁆ = X →
            X ≤ LargeEvenLayer (Subgroup.normalizer (G₀ : Set G) ⊓ Subgroup.centralizer {z})) ∧
        ∀ (H : Type) [Group H], LieModel H .PSL 3 2 f →
          Nat.card ↥(LargeEvenLayer
            (Subgroup.normalizer (G₀ : Set G) ⊓ Subgroup.centralizer {z})) ≤ 3 * Nat.card H

@[expose] def GGSixTrialityDCentralInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ →
    Subgroup.centralizer (ggG0 p B x L D J : Set G) = ⊥ →
    ∀ y ∈ ggM p B x L D J, orderOf y = p →
      GGSixTrialityCase p B x L D J (ggU t n f).D t n f ψ y →
        ∃ d ∈ D, d ≠ 1 ∧ GGPCentralIn p (ggM p B x L D J) d

end Inputs

end CFSG.StandardType
