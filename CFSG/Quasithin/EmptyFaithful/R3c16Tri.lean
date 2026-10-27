module

public import CFSG.Quasithin.EmptyFaithful.R3c16Ree
public import CFSG.Quasithin.EmptyFaithful.R3c16TriB

public section

namespace CFSG.Quasithin.R3c16

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Blueprint
open CFSG.Quasithin.R3c10 CFSG.Quasithin.R3c14 CFSG.Quasithin.R3c15
open scoped commutatorElement

section Triality

theorem noThreeAct_of_triality_odd
    {X : Type} [Group X] [Finite X] {f : ℕ} (hodd : Odd f) (hf : 3 ≤ f)
    (h : ChevalleyExceptionalModel X .trialityD4 2 f) : NoThreeAct X :=
  fun {_ _} hT hVT hV4 hTV {_} hyV {_} hk => noThreeAct_triality hodd hf h hT hVT hV4 hTV hyV hk

theorem not_elConfig_of_triality_odd
    {X : Type} [Group X] [Finite X] {f : ℕ} (hodd : Odd f) (hf : 3 ≤ f)
    (h : ChevalleyExceptionalModel X .trialityD4 2 f) : ¬ ElConfig X :=
  not_elConfig_of_noThreeAct (noThreeAct_of_triality_odd hodd hf h)

variable {G : Type} [Group G] [Finite G]

theorem elim15343_of_triality_odd
    {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (c : CtxComp1 T Mc M V₁ V₂ Yp I L t) (o : Concl15343Open T M V₁ V₂ Yp I L)
    (hN : I ≤ Subgroup.normalizer (L : Set G)) (hYL : Yp ≤ L) {f : ℕ} (hodd : Odd f) (hf : 3 ≤ f)
    (h : ChevalleyExceptionalModel (↥L ⧸ Subgroup.center ↥L) .trialityD4 2 f) : False :=
  not_elConfig_of_triality_odd hodd hf h (elConfig_of_ctx1 c o hN hYL)

theorem cl15335_of_triality_odd
    {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G} (h113 : StageLemma14113)
    (c : CtxComp2 T Mc M V₁ V₂ Yp I L t) (hN : I ≤ Subgroup.normalizer (L : Set G))
    (hYL : Yp ≤ L) {f : ℕ} (hodd : Odd f) (hf : 3 ≤ f)
    (h : ChevalleyExceptionalModel (↥L ⧸ Subgroup.center ↥L) .trialityD4 2 f) : False :=
  cl_of_noThreeAct h113 c hN hYL (noThreeAct_of_triality_odd hodd hf h)

end Triality

section Wiring

@[expose] def Lemma115LieRest7 (X : Type) [Group X] : Prop :=
  ∃ f : ℕ, (2 ≤ f ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSp 2 2 f) ∨
      (2 ≤ f ∧ ChevalleyExceptionalModel X .G2 2 f) ∨
      (1 ≤ f ∧ (f = 1 ∨ Even f) ∧ ChevalleyExceptionalModel X .trialityD4 2 f)

theorem lemma115LieRest6_cases_rest7 {X : Type} [Group X] (h : Lemma115LieRest6 X) :
    Lemma115LieRest7 X ∨ ∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ ChevalleyExceptionalModel X .trialityD4 2 f := by
  obtain ⟨f, h1 | h2 | ⟨hf, h3⟩⟩ := h
  · exact Or.inl ⟨f, Or.inl h1⟩
  · exact Or.inl ⟨f, Or.inr (Or.inl h2)⟩
  · rcases Nat.even_or_odd f with he | ho
    · exact Or.inl ⟨f, Or.inr (Or.inr ⟨hf, Or.inr he, h3⟩)⟩
    · by_cases h1 : f = 1
      · exact Or.inl ⟨f, Or.inr (Or.inr ⟨hf, Or.inl h1, h3⟩)⟩
      · exact Or.inr ⟨f, ho, by obtain ⟨b, hb⟩ := ho; omega, h3⟩

@[expose] def Input15343ElimLieRest7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp1 T Mc M V₁ V₂ Yp I L t → Concl15343Open T M V₁ V₂ Yp I L →
      (∀ K : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M K → K ≤ I → K = I) →
        I ≤ Subgroup.normalizer (L : Set G) → I = L ⊔ Sgp153 T V₁ → Yp ≤ L →
          Lemma115LieRest7 (↥L ⧸ Subgroup.center ↥L) → False

theorem input15343ElimLieRest6_of_rest7
    (kR : Input15343ElimLieRest7) : Input15343ElimLieRest6 := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c o hmin hN hIeq hYL hRest
  rcases lemma115LieRest6_cases_rest7 hRest with h7 | ⟨f, hodd, hf, htri⟩
  · exact kR G T Mc M V₁ V₂ Yp I L t c o hmin hN hIeq hYL h7
  · exact elim15343_of_triality_odd c o hN hYL hodd hf htri

theorem input15343ElimLieRest_of_rest7
    (kR : Input15343ElimLieRest7) : Input15343ElimLieRest :=
  input15343ElimLieRest_of_rest6 (input15343ElimLieRest6_of_rest7 kR)

@[expose] def Lemma115LieHighRest6 (X : Type) [Group X] : Prop :=
  ∃ f : ℕ, (2 ≤ f ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSp 2 2 f) ∨
      (2 ≤ f ∧ ChevalleyExceptionalModel X .G2 2 f) ∨
      (1 ≤ f ∧ (f = 1 ∨ Even f) ∧ ChevalleyExceptionalModel X .trialityD4 2 f)

theorem lemma115LieHighRest5_cases_rest6 {X : Type} [Group X] (h : Lemma115LieHighRest5 X) :
    Lemma115LieHighRest6 X ∨ ∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ ChevalleyExceptionalModel X .trialityD4 2 f := by
  obtain ⟨f, h1 | h2 | ⟨hf, h3⟩⟩ := h
  · exact Or.inl ⟨f, Or.inl h1⟩
  · exact Or.inl ⟨f, Or.inr (Or.inl h2)⟩
  · rcases Nat.even_or_odd f with he | ho
    · exact Or.inl ⟨f, Or.inr (Or.inr ⟨hf, Or.inr he, h3⟩)⟩
    · by_cases h1 : f = 1
      · exact Or.inl ⟨f, Or.inr (Or.inr ⟨hf, Or.inl h1, h3⟩)⟩
      · exact Or.inr ⟨f, ho, by obtain ⟨b, hb⟩ := ho; omega, h3⟩

@[expose] def Input15335CloseLieRest6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp2 T Mc M V₁ V₂ Yp I L t →
      (∀ K : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M K → K ≤ I → K = I) →
        I ≤ Subgroup.normalizer (L : Set G) → I = L ⊔ Sgp153 T V₁ → Yp ≤ L →
          Lemma115LieHighRest6 (↥L ⧸ Subgroup.center ↥L) → False

theorem input15335CloseLieRest5_of_rest6
    (h113 : StageLemma14113) (kR : Input15335CloseLieRest6) : Input15335CloseLieRest5 := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hmin hN hIeq hYL hRest
  rcases lemma115LieHighRest5_cases_rest6 hRest with h6 | ⟨f, hodd, hf, htri⟩
  · exact kR G T Mc M V₁ V₂ Yp I L t c hmin hN hIeq hYL h6
  · exact cl15335_of_triality_odd h113 c hN hYL hodd hf htri

theorem input15335CloseLieRest_of_rest6
    (h113 : StageLemma14113) (kR : Input15335CloseLieRest6) : Input15335CloseLieRest :=
  input15335CloseLieRest_of_rest5 h113 (input15335CloseLieRest5_of_rest6 h113 kR)

end Wiring

end CFSG.Quasithin.R3c16
