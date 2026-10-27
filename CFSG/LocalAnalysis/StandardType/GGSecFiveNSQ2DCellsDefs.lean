module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveNSExclDDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGSecFiveNSQ2DU6Input :
    Prop :=
  GGTBFixInput → GGTBFixNbrXInput → GGLBalanceInput → GGStdSubPrimeInput →
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → ¬ GGSplitLie p L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → GGIsWeylMatrixD M →
        (∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6) →
        ∀ i j : ι, i ≠ j → M.M i j = 2 → ¬ GGOrbPair L Bs 𝒦 M e i j →
          ¬ GGInnerDiagOnLabel (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) p Bs L

end CFSG.StandardType

end
