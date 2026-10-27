module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyQSplit
public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRegionDefs

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly CFSG.LieType.Universal

@[expose] def GGCentralImage
    {G : Type} [Group G] (t : StatedLieTag) (n f : ℕ) (X : Subgroup G) : Prop :=
  ∃ ψ : (ggU t n f).K →* G, StatedLieAdmissible t n 2 f ∧
    ψ.ker ≤ Subgroup.center (ggU t n f).K ∧ ψ.range = X

@[expose] def GGF4QGeFourEndsInput :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp p B Bs x L D J → GGSecFiveWeylCase' p B Bs x D J →
    ¬ GGInnerDiagOnLabel GGLabQTwo p Bs L → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      GGSecFiveRouteCfg p B Bs x L D J {K} → ¬ GGSecFiveTier1Region p B Bs x L D J →
      GGWeylOfType p CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer K Bs) →
        (∃ f, 2 ≤ f ∧ p ∣ 2 ^ f - 1 ∧ GGCentralImage .PSp 3 f L ∧ GGCentralImage .PSp 3 f K) ∨
        (∃ f, 2 ≤ f ∧ p ∣ 2 ^ f - 1 ∧ GGCentralImage .POmegaMinus 4 f L ∧
          (GGCentralImage .PSU 6 f K ∨ GGCentralImage .POmegaMinus 4 f K)) ∨
        (p = 5 ∧ GGCentralImage .POmegaMinus 4 2 L ∧
          (GGCentralImage .PSL 6 2 K ∨ GGCentralImage .POmegaMinus 4 2 K))

@[expose] def GGF4QGeFourF4Input :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp p B Bs x L D J → GGSecFiveWeylCase' p B Bs x D J →
    ¬ GGInnerDiagOnLabel GGLabQTwo p Bs L → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      GGSecFiveRouteCfg p B Bs x L D J {K} → GGWeylOfType p CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer K Bs) →
      ∀ f, 2 ≤ f → p ∣ 2 ^ f - 1 → GGCentralImage .PSp 3 f L → GGCentralImage .PSp 3 f K →
        GGCentralImage .F4 0 f (ggG0 p B x L D J)

@[expose] def GGF4QGeFourTwE6Input :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp p B Bs x L D J → GGSecFiveWeylCase' p B Bs x D J →
    ¬ GGInnerDiagOnLabel GGLabQTwo p Bs L → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      GGSecFiveRouteCfg p B Bs x L D J {K} → GGWeylOfType p CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer K Bs) →
      ∀ f, 2 ≤ f → p ∣ 2 ^ f - 1 → GGCentralImage .POmegaMinus 4 f L →
        (GGCentralImage .PSU 6 f K ∨ GGCentralImage .POmegaMinus 4 f K) →
          GGCentralImage .twistedE6 0 f (ggG0 p B x L D J)

@[expose] def GGF4QGeFourE6FourRouteInput :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp 5 B Bs x L D J → GGSecFiveWeylCase' 5 B Bs x D J →
    ¬ GGInnerDiagOnLabel GGLabQTwo 5 Bs L → ∀ (y : G) (K : Subgroup G), GGNbr 5 B x D J y K →
      GGSecFiveRouteCfg 5 B Bs x L D J {K} →
      GGWeylOfType 5 CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer K Bs) →
      GGCentralImage .POmegaMinus 4 2 L →
        (GGCentralImage .PSL 6 2 K ∨ GGCentralImage .POmegaMinus 4 2 K) →
          GGCentralImage .E6 0 2 (ggG0 5 B x L D J)

end CFSG.StandardType

end
