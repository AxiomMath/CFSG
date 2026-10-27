module

public import CFSG.LocalAnalysis.StandardType.GGQTwoModel
public import CFSG.LocalAnalysis.StandardType.GGQTwoPairsDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoLin
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNormalClosure

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGQTwoModelInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGQTwoSetting p B Bs x L D J → GGQTwoI1 Bs D J → ∀ [Fact p.Prime] (y : G) (K : Subgroup G),
      GGNbr p B x D J y K →
        GGQTwoTwoNodeRowAt p L J ∨ GGQTwoTwoNodeRowAt p K J ∨
          Nonempty (GGQTwoModel p Bs x y D L J K) ∨
            (GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) ∧
              GGReflGenerated p (ggAutomizer K Bs))

@[expose] def GGQTwoXInLNbrModelInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGQTwoSetting p B Bs x L D J → GGQTwoI1 Bs D J → x ∈ L → ∀ [Fact p.Prime],
      ∃ (y : G) (K : Subgroup G), GGNbr p B x D J y K ∧
        Nonempty (GGQTwoModel p Bs x y D L J K)

@[expose] def GGQTwoNoTwoNodeIndInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGQTwoSetting p B Bs x L D J → GGQTwoI1 Bs D J → ∀ [Fact p.Prime] (y : G) (K : Subgroup G),
      GGNbr p B x D J y K →
        (GGQTwoTwoNodeRowAt p L J → x ∉ L) ∧ (GGQTwoTwoNodeRowAt p K J → y ∉ K)

@[expose] def GGQTwoLemma895Prime : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGQTwoSetting p B Bs x L D J → ∀ u : ↥Bs, (u : G) ∈ D → u ≠ 1 → GGTrivialLine p B x D J u →
      ¬ 4 ∣ Nat.card (ggAutomizer J Bs) → GGGammaAt p B Bs x L D J u

@[expose] def GGQTwoNoWeylA3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGQTwoSetting p B Bs x L D J → ∀ [Fact p.Prime] (y : G) (K : Subgroup G),
      GGNbr p B x D J y K → ∀ M : GGQTwoModel p Bs x y D L J K,
        Fintype.card M.ι = 4 → Nat.card (ggAutomizer L Bs) ≠ 24

@[expose] def GGQTwoCentralizerInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGQTwoSetting p B Bs x L D J →
      ∀ j ∈ J, j ∈ Subgroup.centralizer (Bs : Set G) → IsPGroup p (Subgroup.zpowers j) → j ∈ Bs

end CFSG.StandardType

end
