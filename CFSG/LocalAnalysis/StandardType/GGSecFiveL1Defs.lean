module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePrimDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Quasithin

@[expose] def GGSecFiveRankOneInPerfInput :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → GGSplitLie p L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → (∀ i j : ι, i ≠ j → M.M i j ≤ 3) →
        ∀ X : Subgroup G, (X = L ∨ X ∈ 𝒦) → GGSplitLie p X →
          ∀ r ∈ ggAutomizer X Bs, r ∈ ggCoxRefl M e →
            ⁅ggRankOneIn X Bs r, ggRankOneIn X Bs r⁆ = ggRankOneIn X Bs r

@[expose] def GGSecFiveL1PiInput :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → GGSplitLie p L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → (∀ i j : ι, i ≠ j → M.M i j ≤ 3) →
        ∀ X : Subgroup G, (X = L ∨ X ∈ 𝒦) → GGSplitLie p X →
          ∀ r ∈ ggAutomizer X Bs, r ∈ ggCoxRefl M e →
            ggRankOnePerf Bs r ≤ ggRankOneIn X Bs r ⊔ Subgroup.centralizer (X : Set G)

@[expose] def GGSecFiveL1OddInput :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → GGSplitLie p L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → (∀ i j : ι, i ≠ j → M.M i j ≤ 3) →
        ∀ X : Subgroup G, (X = L ∨ X ∈ 𝒦) → GGSplitLie p X →
          ∀ r ∈ ggAutomizer X Bs, r ∈ ggCoxRefl M e →
            Odd (Nat.card ↥(Subgroup.centralizer (X : Set G) ⊓
              Subgroup.centralizer (ggHyperplane Bs r : Set G)))

end CFSG.StandardType
