module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1WeylE

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.ClassicalInvolution.WeakCT

section EInputs

@[expose] def GGSecFiveIdentEInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → GGSplitLie p L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → GGIsWeylMatrixE M →
          ∃ (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G), 3 ≤ bnRank t n ∧
            GGPresentsG0 (L ⊔ ⨆ K ∈ 𝒦, K) (ggU t n f).D t n f ψ

end EInputs

end CFSG.StandardType

end
