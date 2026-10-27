module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveQTwoCompat
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanARowDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveDataResDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1WeylE

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal

@[expose] def GGSecFiveRowJoinOffQAt
    (T : ∀ {ι : Type}, CoxeterMatrix ι → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J → ¬ GGSecFiveQTwoCell p B Bs x L D J →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → T M →
        ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K

@[expose] def GGSecFiveJoinOrderSixAt {G : Type} [Group G] [Finite G] (p : ℕ) (L Bs : Subgroup G)
    (𝒦 : Finset (Subgroup G)) {ι : Type} (M : CoxeterMatrix ι)
    (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)) : Prop :=
  GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e ∧
    ((∃ (m : ℕ) (σ : Fin m ≃ ι), 5 ≤ m ∧ M = (CoxeterMatrix.A m).reindex σ) ∨
      GGIsWeylMatrixD M ∨ GGIsWeylMatrixE M) ∧
    ∃ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e ∧ Nat.card (ggRankOneIn L Bs r) = 6

@[expose] def GGSecFiveCompatRestWResNJoinInput :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J → ¬ GGSecFivePhanARow p B Bs x L D J →
      ∀ (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
        GGPresentsG0 (ggG0 p B x L D J) (ggU t n f).D t n f ψ →
          (GGSecFiveQTwoCell p B Bs x L D J ∨
            Nat.card (↥(L ⊔ ⨆ K ∈ 𝒦, K) ⧸ Subgroup.center ↥(L ⊔ ⨆ K ∈ 𝒦, K)) =
              Nat.card (↥(ggG0 p B x L D J) ⧸ Subgroup.center ↥(ggG0 p B x L D J)) ∨
            ∃ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
              GGSecFiveJoinOrderSixAt p L Bs 𝒦 M e) →
            GGSecFiveCompat p B x L D J

end CFSG.StandardType

end
