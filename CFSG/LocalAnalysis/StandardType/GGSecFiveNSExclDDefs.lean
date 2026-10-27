module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveJA2PhanDDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrEnnola
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
public import CFSG.LocalAnalysis.StandardType.GGTBFixDefs
public import CFSG.LocalAnalysis.StandardType.GGTBFixNbrDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan

@[expose] def GGSecFiveNSEnnolaDInput :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → ¬ GGSplitLie p L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → GGIsWeylMatrixD M →
        ∀ i j : ι, i ≠ j → M.M i j = 2 → ¬ GGOrbPair L Bs 𝒦 M e i j →
          ¬ GGInnerDiagOnLabel (fun p lab => ggRowP_Ennola p lab ∧ ¬ ggRowP_ESU p lab) p Bs L

@[expose] def GGSecFiveNSQ2DInput :
    Prop :=
  GGTBFixInput → GGTBFixNbrXInput → GGLBalanceInput → GGStdSubPrimeInput →
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → ¬ GGSplitLie p L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → GGIsWeylMatrixD M →
        (∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6) →
        ∀ i j : ι, i ≠ j → M.M i j = 2 → ¬ GGOrbPair L Bs 𝒦 M e i j →
          ¬ GGInnerDiagOnLabel
            (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ (lab.rank = 3 ∨ lab.rank = 5)) p Bs L

end CFSG.StandardType

end
