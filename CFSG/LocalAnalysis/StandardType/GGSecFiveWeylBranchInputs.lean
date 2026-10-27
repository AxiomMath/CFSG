module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinPrimed

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGSecFiveJA2Input
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg' p B Bs x L D J 𝒦 → GGSplitLie p L →
      ∃ r ∈ ggAutomizer J Bs, ∃ r' ∈ ggAutomizer J Bs, GGIsReflection p r ∧
        GGIsReflection p r' ∧ orderOf (r * r') = 3

@[expose] def GGSecFiveOrthExclInput
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg' p B Bs x L D J 𝒦 → GGSplitLie p L →
      (∀ b : ↥Bs, (∀ φ ∈ ggAInf p B Bs x L D J, φ b = b) → b = 1) → p = 3 →
        ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V] (Q : QuadraticForm (ZMod p) V),
          (QuadraticMap.polarBilin Q).Nondegenerate → ∀ [Fact p.Prime] (ι : Additive ↥Bs ≃+ V),
          (Module.finrank (ZMod p) V = 4 ∨ Module.finrank (ZMod p) V = 5) →
          (∀ g : V ≃ₗ[ZMod p] V, (∃ a ∈ ggAInf p B Bs x L D J, ggLin (p := p) ι a = g) ↔
            ∀ v, Q (g v) = Q v) →
          GGWeylReflectionGroup p (ggAInf p B Bs x L D J)

end CFSG.StandardType

end
