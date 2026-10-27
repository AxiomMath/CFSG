module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal

section JoinHC

@[expose] def GGSecFiveJoinHCInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ∀ (t₀ : StatedLieTag) (n₀ f₀ : ℕ) (ψ₀ : (ggU t₀ n₀ f₀).K →* G),
        GGPresentsG0 (ggG0 p B x L D J) (ggU t₀ n₀ f₀).D t₀ n₀ f₀ ψ₀ →
          Nat.card (↥(L ⊔ ⨆ K ∈ 𝒦, K) ⧸ Subgroup.center ↥(L ⊔ ⨆ K ∈ 𝒦, K)) =
            Nat.card (↥(ggG0 p B x L D J) ⧸ Subgroup.center ↥(ggG0 p B x L D J))

end JoinHC

end CFSG.StandardType

end
