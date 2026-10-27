module

public import CFSG.LocalAnalysis.StandardType.GGTBFix
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyQSplit
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerCore

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Assembly TableB

@[expose] def GGNbrFixCentralizesInput {ι : Type} (M : CoxeterMatrix ι) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp 3 B Bs x L D J → GGSecFiveWeylCase 3 B Bs x D J →
    GGInnerDiagOnLabel GGLabQTwo 3 Bs L →
    ∀ (y : G) (K : Subgroup G), GGNbr 3 B x D J y K →
      GGWeylOfType 3 M (ggAutomizer L Bs ⊔ ggAutomizer K Bs) →
      ∀ b : Bs, (∀ φ ∈ ggAutomizer K Bs, φ b = b) → (b : G) ∈ Subgroup.centralizer (K : Set G)

@[expose] def GGNbrRankInput {ι : Type} (M : CoxeterMatrix ι) (n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp 3 B Bs x L D J → GGSecFiveWeylCase 3 B Bs x D J →
    GGInnerDiagOnLabel GGLabQTwo 3 Bs L →
    ∀ (y : G) (K : Subgroup G), GGNbr 3 B x D J y K →
      GGWeylOfType 3 M (ggAutomizer L Bs ⊔ ggAutomizer K Bs) →
      ∀ hBsN : Bs ≤ Subgroup.normalizer (K : Set G), 3 ^ (n - 2) ≤ Nat.card (ggGamma K hBsN).range

@[expose] def GGFrameBstarLowerInput {ι : Type} (M : CoxeterMatrix ι) (n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp 3 B Bs x L D J → GGSecFiveWeylCase 3 B Bs x D J →
    GGSecFiveWeylAt 3 B Bs x L D J M → GGInnerDiagOnLabel GGLabQTwo 3 Bs L →
      3 ^ n ≤ Nat.card Bs

@[expose] def GGNbrNoFixMarkedInput {ι : Type} (M : CoxeterMatrix ι) (n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp 3 B Bs x L D J → GGSecFiveWeylCase 3 B Bs x D J →
    GGInnerDiagOnLabel GGLabQTwo 3 Bs L →
    ∀ (y : G) (K : Subgroup G), GGNbr 3 B x D J y K →
      GGWeylOfType 3 M (ggAutomizer L Bs ⊔ ggAutomizer K Bs) →
      LargeEvenMarking K (fun _ R _ I _ θ => Bs ≤ Subgroup.normalizer (K : Set G) ∧
        (∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) ∧
        GGTorusNoFix 3 (n - 2) R I)

@[expose] def GGNbrNoFixInput {ι : Type} (M : CoxeterMatrix ι) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp 3 B Bs x L D J → GGSecFiveWeylCase 3 B Bs x D J →
    GGInnerDiagOnLabel GGLabQTwo 3 Bs L →
    ∀ (y : G) (K : Subgroup G), GGNbr 3 B x D J y K →
      GGWeylOfType 3 M (ggAutomizer L Bs ⊔ ggAutomizer K Bs) →
      LargeEvenMarking K (fun _ R _ I _ θ => ∃ hBsN : Bs ≤ Subgroup.normalizer (K : Set G),
        (∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) ∧
        ∃ r : ℕ, 3 ≤ r ∧ 3 ^ r ≤ Nat.card (ggGamma K hBsN).range ∧ GGTorusNoFix 3 r R I)

end CFSG.StandardType.FrameRoute
