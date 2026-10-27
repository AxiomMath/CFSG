module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanPrimDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan

@[expose] def GGSecFiveL2PhanDInput :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → ¬ GGSplitLie p L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → GGIsWeylMatrixD M →
        (∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6) →
        ∀ i j : ι, i ≠ j → M.M i j = 2 → ¬ GGOrbPair L Bs 𝒦 M e i j →
          ∀ a ∈ ggRankOnePerf Bs ((e (M.simple i) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs),
          ∀ b ∈ ggRankOnePerf Bs ((e (M.simple j) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs),
            a * b = b * a

end CFSG.StandardType

end
