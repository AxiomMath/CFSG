module

public import CFSG.Quasithin.EmptyFaithful.SzN27CompA
public import CFSG.Quasithin.EmptyFaithful.R3c17C

public section

namespace CFSG.Quasithin.R3c17

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin.R3c10
  CFSG.Quasithin.R3c14 CFSG.Quasithin.R3c15

@[expose] def Lemma115LieRest10 (X : Type) [Group X] : Prop :=
  ∃ f : ℕ, 2 ≤ f ∧ ChevalleyExceptionalModel X .G2 2 f

theorem lemma115LieRest9_cases_rest10 {X : Type} [Group X] (h : SzN27.Lemma115LieRest9 X) :
    Lemma115LieRest10 X ∨ ∃ f : ℕ, 2 ≤ f ∧ ChevalleyExceptionalModel X .trialityD4 2 f := by
  obtain ⟨f, ⟨hf, h1⟩ | ⟨hf, -, h2⟩⟩ := h
  · exact Or.inl ⟨f, hf, h1⟩
  · exact Or.inr ⟨f, hf, h2⟩

@[expose] def Input15343ElimLieRest10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp1 T Mc M V₁ V₂ Yp I L t → Concl15343Open T M V₁ V₂ Yp I L →
      (∀ K : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M K → K ≤ I → K = I) →
        I ≤ Subgroup.normalizer (L : Set G) → I = L ⊔ Sgp153 T V₁ → Yp ≤ L →
          Lemma115LieRest10 (↥L ⧸ Subgroup.center ↥L) → False

theorem input15343ElimLieRest9_of_rest10
    (kR : Input15343ElimLieRest10) : SzN27.Input15343ElimLieRest9 := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c o hmin hN hIeq hYL hRest
  rcases lemma115LieRest9_cases_rest10 hRest with h10 | ⟨f, hf, htri⟩
  · exact kR G T Mc M V₁ V₂ Yp I L t c o hmin hN hIeq hYL h10
  · exact elim15343_of_triality_scalar c o hN hYL hf htri

theorem input15343ElimLieRest_of_rest10
    (kR : Input15343ElimLieRest10) : R3c10.Input15343ElimLieRest :=
  SzN27.input15343ElimLieRest_of_rest9 (input15343ElimLieRest9_of_rest10 kR)

end CFSG.Quasithin.R3c17
