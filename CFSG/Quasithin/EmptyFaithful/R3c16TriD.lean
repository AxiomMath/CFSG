module

public import CFSG.Quasithin.EmptyFaithful.R3c16Tri
public import CFSG.Quasithin.EmptyFaithful.R3c16TriC

public section

namespace CFSG.Quasithin.R3c16

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Blueprint
open CFSG.Quasithin.R3c10 CFSG.Quasithin.R3c14 CFSG.Quasithin.R3c15
open scoped commutatorElement

section Elim

@[expose] def Lemma115LieRest8 (X : Type) [Group X] : Prop :=
  ∃ f : ℕ, (2 ≤ f ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSp 2 2 f) ∨
      (2 ≤ f ∧ ChevalleyExceptionalModel X .G2 2 f) ∨
      (2 ≤ f ∧ Even f ∧ ChevalleyExceptionalModel X .trialityD4 2 f)

theorem lemma115LieRest7_cases_rest8 {X : Type} [Group X] (h : Lemma115LieRest7 X) :
    Lemma115LieRest8 X ∨ ChevalleyExceptionalModel X .trialityD4 2 1 := by
  obtain ⟨f, h1 | h2 | ⟨hf, hf', h3⟩⟩ := h
  · exact Or.inl ⟨f, Or.inl h1⟩
  · exact Or.inl ⟨f, Or.inr (Or.inl h2)⟩
  · rcases hf' with rfl | he
    · exact Or.inr h3
    · exact Or.inl ⟨f, Or.inr (Or.inr ⟨by obtain ⟨b, hb⟩ := he; omega, he, h3⟩)⟩

@[expose] def Input15343ElimLieRest8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp1 T Mc M V₁ V₂ Yp I L t → Concl15343Open T M V₁ V₂ Yp I L →
      (∀ K : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M K → K ≤ I → K = I) →
        I ≤ Subgroup.normalizer (L : Set G) → I = L ⊔ Sgp153 T V₁ → Yp ≤ L →
          Lemma115LieRest8 (↥L ⧸ Subgroup.center ↥L) → False

theorem input15343ElimLieRest7_of_rest8
    (kR : Input15343ElimLieRest8) : Input15343ElimLieRest7 := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c o hmin hN hIeq hYL hRest
  rcases lemma115LieRest7_cases_rest8 hRest with h8 | htri
  · exact kR G T Mc M V₁ V₂ Yp I L t c o hmin hN hIeq hYL h8
  · exact elim15343_of_triality_one c o hN hYL htri

theorem input15343ElimLieRest_of_rest8
    (kR : Input15343ElimLieRest8) : Input15343ElimLieRest :=
  input15343ElimLieRest_of_rest7 (input15343ElimLieRest7_of_rest8 kR)

end Elim

section Cl

@[expose] def Lemma115LieHighRest7 (X : Type) [Group X] : Prop :=
  ∃ f : ℕ, (2 ≤ f ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSp 2 2 f) ∨
      (2 ≤ f ∧ ChevalleyExceptionalModel X .G2 2 f) ∨
      (2 ≤ f ∧ Even f ∧ ChevalleyExceptionalModel X .trialityD4 2 f)

theorem lemma115LieHighRest6_cases_rest7 {X : Type} [Group X] (h : Lemma115LieHighRest6 X) :
    Lemma115LieHighRest7 X ∨ ChevalleyExceptionalModel X .trialityD4 2 1 := by
  obtain ⟨f, h1 | h2 | ⟨hf, hf', h3⟩⟩ := h
  · exact Or.inl ⟨f, Or.inl h1⟩
  · exact Or.inl ⟨f, Or.inr (Or.inl h2)⟩
  · rcases hf' with rfl | he
    · exact Or.inr h3
    · exact Or.inl ⟨f, Or.inr (Or.inr ⟨by obtain ⟨b, hb⟩ := he; omega, he, h3⟩)⟩

@[expose] def Input15335CloseLieRest7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp2 T Mc M V₁ V₂ Yp I L t →
      (∀ K : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M K → K ≤ I → K = I) →
        I ≤ Subgroup.normalizer (L : Set G) → I = L ⊔ Sgp153 T V₁ → Yp ≤ L →
          Lemma115LieHighRest7 (↥L ⧸ Subgroup.center ↥L) → False

theorem input15335CloseLieRest6_of_rest7
    (h113 : StageLemma14113) (kR : Input15335CloseLieRest7) : Input15335CloseLieRest6 := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hmin hN hIeq hYL hRest
  rcases lemma115LieHighRest6_cases_rest7 hRest with h7 | htri
  · exact kR G T Mc M V₁ V₂ Yp I L t c hmin hN hIeq hYL h7
  · exact cl15335_of_triality_one h113 c hN hYL htri

theorem input15335CloseLieRest_of_rest7
    (h113 : StageLemma14113) (kR : Input15335CloseLieRest7) : Input15335CloseLieRest :=
  input15335CloseLieRest_of_rest6 h113 (input15335CloseLieRest6_of_rest7 h113 kR)

end Cl

end CFSG.Quasithin.R3c16
