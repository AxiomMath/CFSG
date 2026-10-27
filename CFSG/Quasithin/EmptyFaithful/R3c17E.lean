module

public import CFSG.Quasithin.EmptyFaithful.R3c17C
public import CFSG.Quasithin.EmptyFaithful.R3c17D
public import CFSG.Quasithin.EmptyFaithful.R3c16TriD

public section

namespace CFSG.Quasithin.R3c17

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Blueprint
open CFSG.Quasithin.R3c10 CFSG.Quasithin.R3c14 CFSG.Quasithin.R3c15 CFSG.Quasithin.R3c16
open scoped commutatorElement

section Cl

variable {G : Type} [Group G] [Finite G]

theorem cl15335_of_triality_scalar
    {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G} (h113 : StageLemma14113)
    (c : CtxComp2 T Mc M V₁ V₂ Yp I L t) (hN : I ≤ Subgroup.normalizer (L : Set G))
    (hYL : Yp ≤ L) {f : ℕ} (hf : 2 ≤ f)
    (h : ChevalleyExceptionalModel (↥L ⧸ Subgroup.center ↥L) .trialityD4 2 f) : False := by
  rcases c.hyp.cases with hY | hU
  · exact cl_case1_of_centralScalar h113 c hN hYL hY (centralScalar_triality hf h)
  · exact cl15335_case2_of_triality_scalar h113 c hN hYL hU hf h

end Cl

section Wiring

@[expose] def Lemma115LieRest9 (X : Type) [Group X] : Prop :=
  ∃ f : ℕ, (2 ≤ f ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSp 2 2 f) ∨
      (2 ≤ f ∧ ChevalleyExceptionalModel X .G2 2 f)

@[expose] def Input15343ElimLieRest9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp1 T Mc M V₁ V₂ Yp I L t → Concl15343Open T M V₁ V₂ Yp I L →
      (∀ K : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M K → K ≤ I → K = I) →
        I ≤ Subgroup.normalizer (L : Set G) → I = L ⊔ Sgp153 T V₁ → Yp ≤ L →
          Lemma115LieRest9 (↥L ⧸ Subgroup.center ↥L) → False

@[expose] def Lemma115LieHighRest8 (X : Type) [Group X] : Prop :=
  ∃ f : ℕ, (2 ≤ f ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSp 2 2 f) ∨
      (2 ≤ f ∧ ChevalleyExceptionalModel X .G2 2 f)

theorem lemma115LieHighRest7_cases_rest8 {X : Type} [Group X] (h : Lemma115LieHighRest7 X) :
    Lemma115LieHighRest8 X ∨ ∃ f : ℕ, 2 ≤ f ∧ ChevalleyExceptionalModel X .trialityD4 2 f := by
  obtain ⟨f, h1 | h2 | ⟨hf, -, h3⟩⟩ := h
  · exact Or.inl ⟨f, Or.inl h1⟩
  · exact Or.inl ⟨f, Or.inr h2⟩
  · exact Or.inr ⟨f, hf, h3⟩

@[expose] def Input15335CloseLieRest8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp2 T Mc M V₁ V₂ Yp I L t →
      (∀ K : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M K → K ≤ I → K = I) →
        I ≤ Subgroup.normalizer (L : Set G) → I = L ⊔ Sgp153 T V₁ → Yp ≤ L →
          Lemma115LieHighRest8 (↥L ⧸ Subgroup.center ↥L) → False

theorem input15335CloseLieRest7_of_rest8
    (h113 : StageLemma14113) (kR : Input15335CloseLieRest8) : Input15335CloseLieRest7 := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hmin hN hIeq hYL hRest
  rcases lemma115LieHighRest7_cases_rest8 hRest with h8 | ⟨f, hf, htri⟩
  · exact kR G T Mc M V₁ V₂ Yp I L t c hmin hN hIeq hYL h8
  · exact cl15335_of_triality_scalar h113 c hN hYL hf htri

theorem input15335CloseLieRest_of_rest8
    (h113 : StageLemma14113) (kR : Input15335CloseLieRest8) : Input15335CloseLieRest :=
  input15335CloseLieRest_of_rest7 h113 (input15335CloseLieRest7_of_rest8 h113 kR)

end Wiring

end CFSG.Quasithin.R3c17
