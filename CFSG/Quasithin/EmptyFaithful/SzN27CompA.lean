module

public import CFSG.Quasithin.EmptyFaithful.SzN27Sp4E
public import CFSG.Quasithin.EmptyFaithful.R3c16TriD

public section

namespace CFSG.Quasithin.SzN27

open CFSG.Quasithin CFSG.Quasithin.R3c16 CFSG.Blueprint

@[expose] def Lemma115LieRest9 (X : Type) [Group X] : Prop :=
  ∃ f : ℕ, (2 ≤ f ∧ ChevalleyExceptionalModel X .G2 2 f) ∨
      (2 ≤ f ∧ Even f ∧ ChevalleyExceptionalModel X .trialityD4 2 f)

theorem lemma115LieRest8_cases_rest9 {X : Type} [Group X] (h : Lemma115LieRest8 X) :
    Lemma115LieRest9 X ∨
      ∃ f : ℕ, 2 ≤ f ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSp 2 2 f := by
  obtain ⟨f, h1 | h2 | h3⟩ := h
  · exact Or.inr ⟨f, h1⟩
  · exact Or.inl ⟨f, Or.inl h2⟩
  · exact Or.inl ⟨f, Or.inr h3⟩

@[expose] def Input15343ElimLieRest9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp1 T Mc M V₁ V₂ Yp I L t → Concl15343Open T M V₁ V₂ Yp I L →
      (∀ K : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M K → K ≤ I → K = I) →
        I ≤ Subgroup.normalizer (L : Set G) → I = L ⊔ Sgp153 T V₁ → Yp ≤ L →
          Lemma115LieRest9 (↥L ⧸ Subgroup.center ↥L) → False

theorem input15343ElimLieRest8_of_rest9 (kR : Input15343ElimLieRest9) :
    R3c16.Input15343ElimLieRest8 := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c o hmin hN hIeq hYL hRest
  rcases lemma115LieRest8_cases_rest9 hRest with h9 | ⟨f, hf, hsp⟩
  · exact kR G T Mc M V₁ V₂ Yp I L t c o hmin hN hIeq hYL h9
  · exact elim15343_of_sp4 c o hN hYL hf hsp

theorem input15343ElimLieRest_of_rest9
    (kR : Input15343ElimLieRest9) : R3c10.Input15343ElimLieRest :=
  input15343ElimLieRest_of_rest8 (input15343ElimLieRest8_of_rest9 kR)

end CFSG.Quasithin.SzN27
