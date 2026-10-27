module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveL1Defs
public import CFSG.Quasithin.Background.A3Structure38Facts
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGSecFiveKGCentInput :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → GGSplitLie p L →
      ∀ X : Subgroup G, (X = L ∨ X ∈ 𝒦) → GGSplitLie p X →
        ∀ t : G, (∃ k : ℕ, t ^ (2 ^ k) = 1) → t ∈ Subgroup.normalizer (X : Set G) →
          t ∈ Subgroup.centralizer (D : Set G) → t ∈ Subgroup.centralizer (J : Set G) →
            ∀ g ∈ X, ∀ h ∈ X, Commute (t * g * t⁻¹ * g⁻¹) h

@[expose] def GGSecFiveJReflInput :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → GGSplitLie p L →
      ∃ r ∈ ggAutomizer J Bs, GGIsReflection p r

@[expose] def GGSplitLieOutInput :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (X : Subgroup G), GGSplitLie p X →
    CFSG.Quasithin.OutSolvable ↥X

@[expose] def GGSecFiveRk1CentInput :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → GGSplitLie p L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → (∀ i j : ι, i ≠ j → M.M i j ≤ 3) →
        ∀ X : Subgroup G, (X = L ∨ X ∈ 𝒦) → GGSplitLie p X →
          ∀ r ∈ ggAutomizer X Bs, r ∈ ggCoxRefl M e →
            ∀ Q : Subgroup G, Q ≤ Subgroup.centralizer (ggHyperplane Bs r : Set G) →
              ⁅Q, Q⁆ = Q → Q ≤ X ⊔ Subgroup.centralizer (X : Set G) →
                Q ≤ ggRankOneIn X Bs r ⊔ Subgroup.centralizer (X : Set G)

end CFSG.StandardType
