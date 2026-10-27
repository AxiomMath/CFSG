module

public import CFSG.LocalAnalysis.StandardType.GGFrameRouteFSInputs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyQSplit

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Open CFSG.Assembly

@[expose] def GGFrameBstarCardInput {ι : Type} (M : CoxeterMatrix ι) (n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp 3 B Bs x L D J → GGSecFiveWeylCase 3 B Bs x D J →
    GGSecFiveWeylAt 3 B Bs x L D J M → GGInnerDiagOnLabel GGLabQTwo 3 Bs L →
      Nat.card Bs = 3 ^ n

@[expose] def GGFrameA4Input {ι : Type} (M : CoxeterMatrix ι) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp 3 B Bs x L D J → GGSecFiveWeylCase 3 B Bs x D J →
    GGSecFiveWeylAt 3 B Bs x L D J M → GGInnerDiagOnLabel GGLabQTwo 3 Bs L →
      ∀ y : G, y ∈ B → y ≠ 1 →
        ∃ g : G, g * y * g⁻¹ ∈ Subgroup.centralizer ({y} : Set G) ∧
          g * y * g⁻¹ ∉ Subgroup.zpowers y

end CFSG.StandardType.FrameRoute

end
