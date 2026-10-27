module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinPrimed

public section

namespace CFSG.StandardType

@[expose] def GGSecFiveWeylInfAt (T : ∀ {ι : Type}, CoxeterMatrix ι → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → T M →
          GGWeylReflectionGroup p (ggAInf p B Bs x L D J)

@[expose] def GGSecFiveReflMaxAt (T : ∀ {ι : Type}, CoxeterMatrix ι → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → T M →
          ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
            ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦

end CFSG.StandardType

end
