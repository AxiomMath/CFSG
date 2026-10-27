module

public import CFSG.Quasithin.EmptyFaithful.S153D26

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement

@[expose] def Input26Component : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I : Subgroup G) (t : G),
    Ctx15325 T Mc M V₁ V₂ Yp I t → Facts15325 T Mc M V₁ V₂ Yp I →
      ∃ L : Subgroup G, L ∈ cComp (thompsonJ I) ∧ ¬ L ≤ M ⊓ I ∧ 1 ≤ CFSG.Open.pRank 3 L ∧
        CFSG.IsQuasisimple ↥(autOn L (UI153 T I)) ∧ B56QuasisimpleList ↥(autOn L (UI153 T I))

@[expose] def Input26Quasisimple : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I : Subgroup G) (t : G),
    Ctx15325 T Mc M V₁ V₂ Yp I t → Facts15325 T Mc M V₁ V₂ Yp I →
      ∀ L : Subgroup G, L ∈ cComp (thompsonJ I) → ¬ L ≤ M ⊓ I →
        CFSG.IsQuasisimple ↥(autOn L (UI153 T I)) → B56QuasisimpleList ↥(autOn L (UI153 T I)) →
          CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)

theorem input15326Two_of_narrow (h1 : Input26Component) (h2 : Input26Quasisimple) :
    Input15326Two := by
  intro G _ _ T Mc M V₁ V₂ Yp I t c hF
  obtain ⟨L, hLc, hLn, hL3, hLq, hLl⟩ := h1 G T Mc M V₁ V₂ Yp I t c hF
  exact ⟨L, hLc, hLn, hL3, hLq, h2 G T Mc M V₁ V₂ Yp I t c hF L hLc hLn hLq hLl⟩

end CFSG.Quasithin
