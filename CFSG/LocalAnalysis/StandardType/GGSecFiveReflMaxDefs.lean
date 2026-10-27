module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinPrimed

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGSecFiveInfWitness {G : Type} [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) : Prop :=
  GGWeylReflectionGroup p (ggAInf p B Bs x L D J) ∧
    ∃ 𝒦' : Finset (Subgroup G), GGNbrSet p B x D J 𝒦' ∧ ggAutomizerJoin L Bs 𝒦' = ggAInf p B Bs x L D J

@[expose] def GGSecFiveNbrAutFamily {G : Type} [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (D J : Subgroup G) : Set (Subgroup (MulAut ↥Bs)) :=
  {S | ∃ (y : G) (K : Subgroup G), GGNbr p B x D J y K ∧ S = ggAutomizer K Bs}

@[expose] def GGSecFiveCaseZeroInput
        : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg' p B Bs x L D J 𝒦 → GGSplitLie p L →
      ∀ hxBs : x ∈ Bs, (∀ φ ∈ ggAInf p B Bs x L D J, φ ⟨x, hxBs⟩ = ⟨x, hxBs⟩) →
        (∃ (y : G) (K : Subgroup G), GGNbr p B x D J y K ∧
          ∃ t ∈ ggAutomizer K Bs, GGIsReflection p t ∧ ¬ GGRealized p Bs t) →
          GGSecFiveInfWitness p B Bs x L D J

end CFSG.StandardType

end
