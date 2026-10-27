module

public import CFSG.Quasithin.EmptyFaithful.R3c16Main
public import CFSG.Quasithin.EmptyFaithful.R3c16Cl
public import CFSG.Quasithin.EmptyFaithful.R3c16Act
public import CFSG.Quasithin.EmptyFaithful.R3c16ReeB

public section

namespace CFSG.Quasithin.R3c16

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Blueprint
open CFSG.Quasithin.R3c10 CFSG.Quasithin.R3c14 CFSG.Quasithin.R3c15
open scoped commutatorElement

section Ree

theorem noThreeAct_of_ree
    {X : Type} [Group X] [Finite X] {f : ℕ} (h : ReeTitsModel X .twistedF4 2 f) : NoThreeAct X :=
  fun {_ _} hT hVT hV4 hTV {_} hyV {_} hk => noThreeAct_ree h hT hVT hV4 hTV hyV hk

theorem not_elConfig_of_ree
    {X : Type} [Group X] [Finite X] {f : ℕ} (h : ReeTitsModel X .twistedF4 2 f) : ¬ ElConfig X :=
  not_elConfig_of_noThreeAct (noThreeAct_of_ree h)

variable {G : Type} [Group G] [Finite G]

theorem elim15343_of_ree
    {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (c : CtxComp1 T Mc M V₁ V₂ Yp I L t) (o : Concl15343Open T M V₁ V₂ Yp I L)
    (hN : I ≤ Subgroup.normalizer (L : Set G)) (hYL : Yp ≤ L) {f : ℕ}
    (h : ReeTitsModel (↥L ⧸ Subgroup.center ↥L) .twistedF4 2 f) : False :=
  not_elConfig_of_ree h (elConfig_of_ctx1 c o hN hYL)

theorem cl15335_of_ree
    {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G} (h113 : StageLemma14113)
    (c : CtxComp2 T Mc M V₁ V₂ Yp I L t) (hN : I ≤ Subgroup.normalizer (L : Set G))
    (hYL : Yp ≤ L) {f : ℕ} (h : ReeTitsModel (↥L ⧸ Subgroup.center ↥L) .twistedF4 2 f) : False :=
  cl_of_noThreeAct h113 c hN hYL (noThreeAct_of_ree h)

end Ree

section Wiring

@[expose] def Lemma115LieRest6 (X : Type) [Group X] : Prop :=
  ∃ f : ℕ, (2 ≤ f ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSp 2 2 f) ∨
      (2 ≤ f ∧ ChevalleyExceptionalModel X .G2 2 f) ∨
      (1 ≤ f ∧ ChevalleyExceptionalModel X .trialityD4 2 f)

theorem lemma115LieRest5_cases_rest6 {X : Type} [Group X] (h : Lemma115LieRest5 X) :
    Lemma115LieRest6 X ∨ ∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ ReeTitsModel X .twistedF4 2 f := by
  obtain ⟨f, h1 | h2 | h3 | h4⟩ := h
  · exact Or.inl ⟨f, Or.inl h1⟩
  · exact Or.inl ⟨f, Or.inr (Or.inl h2)⟩
  · exact Or.inl ⟨f, Or.inr (Or.inr h3)⟩
  · exact Or.inr ⟨f, h4⟩

@[expose] def Input15343ElimLieRest6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp1 T Mc M V₁ V₂ Yp I L t → Concl15343Open T M V₁ V₂ Yp I L →
      (∀ K : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M K → K ≤ I → K = I) →
        I ≤ Subgroup.normalizer (L : Set G) → I = L ⊔ Sgp153 T V₁ → Yp ≤ L →
          Lemma115LieRest6 (↥L ⧸ Subgroup.center ↥L) → False

theorem input15343ElimLieRest5_of_rest6
    (kR : Input15343ElimLieRest6) : Input15343ElimLieRest5 := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c o hmin hN hIeq hYL hRest
  rcases lemma115LieRest5_cases_rest6 hRest with h6 | ⟨f, -, -, hree⟩
  · exact kR G T Mc M V₁ V₂ Yp I L t c o hmin hN hIeq hYL h6
  · exact elim15343_of_ree c o hN hYL hree

theorem input15343ElimLieRest_of_rest6
    (kR : Input15343ElimLieRest6) : Input15343ElimLieRest :=
  input15343ElimLieRest_of_rest5 (input15343ElimLieRest5_of_rest6 kR)

@[expose] def Lemma115LieHighRest5 (X : Type) [Group X] : Prop :=
  ∃ f : ℕ, (2 ≤ f ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSp 2 2 f) ∨
      (2 ≤ f ∧ ChevalleyExceptionalModel X .G2 2 f) ∨
      (1 ≤ f ∧ ChevalleyExceptionalModel X .trialityD4 2 f)

theorem lemma115LieHighRest4_cases_rest5 {X : Type} [Group X] (h : Lemma115LieHighRest4 X) :
    Lemma115LieHighRest5 X ∨ ∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ ReeTitsModel X .twistedF4 2 f := by
  obtain ⟨f, h1 | h2 | h3 | h4⟩ := h
  · exact Or.inl ⟨f, Or.inl h1⟩
  · exact Or.inl ⟨f, Or.inr (Or.inl h2)⟩
  · exact Or.inl ⟨f, Or.inr (Or.inr h3)⟩
  · exact Or.inr ⟨f, h4⟩

@[expose] def Input15335CloseLieRest5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp2 T Mc M V₁ V₂ Yp I L t →
      (∀ K : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M K → K ≤ I → K = I) →
        I ≤ Subgroup.normalizer (L : Set G) → I = L ⊔ Sgp153 T V₁ → Yp ≤ L →
          Lemma115LieHighRest5 (↥L ⧸ Subgroup.center ↥L) → False

theorem input15335CloseLieRest4_of_rest5
    (h113 : StageLemma14113) (kR : Input15335CloseLieRest5) : Input15335CloseLieRest4 := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hmin hN hIeq hYL hRest
  rcases lemma115LieHighRest4_cases_rest5 hRest with h5 | ⟨f, -, -, hree⟩
  · exact kR G T Mc M V₁ V₂ Yp I L t c hmin hN hIeq hYL h5
  · exact cl15335_of_ree h113 c hN hYL hree

theorem input15335CloseLieRest_of_rest5
    (h113 : StageLemma14113) (kR : Input15335CloseLieRest5) : Input15335CloseLieRest :=
  input15335CloseLieRest_of_rest4 h113 (input15335CloseLieRest4_of_rest5 h113 kR)

end Wiring

end CFSG.Quasithin.R3c16
