module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylB

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGSpJoinAutInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (y : G) (K : Subgroup G), GGConfig p B Bs x L D J → GGOpAutTrivial p Bs →
    GGInnerDiagAll p B Bs x L D J → GGNoTransvection p Bs → GGTypeCNbr p B Bs x L D J n f y K →
    ∀ (y' : G) (K' : Subgroup G), GGNbr p B x D J y' K' →
      ggAutomizer K' Bs ≤ ggAutomizer L Bs ⊔ ggAutomizer K Bs → K' ≤ L ⊔ K

@[expose] def GGSpJoinReflInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (y : G) (K : Subgroup G), GGConfig p B Bs x L D J → GGOpAutTrivial p Bs →
    GGInnerDiagAll p B Bs x L D J → GGNoTransvection p Bs → GGTypeCNbr p B Bs x L D J n f y K →
    ∀ (y' : G) (K' : Subgroup G), GGNbr p B x D J y' K' →
      ggAutomizer K' Bs ≤ ggAutomizer L Bs ⊔ ggAutomizer K Bs

theorem ggSpJoinInput_of_aut_refl (h₁ : GGSpJoinAutInput) (h₂ : GGSpJoinReflInput) :
    GGSpJoinInput := by
  intro G _ _ p B Bs x L D J n f y K hcfg hOp hInn hNoTr hN y' K' hK'
  exact h₁ G p B Bs x L D J n f y K hcfg hOp hInn hNoTr hN y' K' hK'
    (h₂ G p B Bs x L D J n f y K hcfg hOp hInn hNoTr hN y' K' hK')

end CFSG.StandardType
