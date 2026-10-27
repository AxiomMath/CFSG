module

public import CFSG.Quasithin.EmptyFaithful.R3c15Cl
public import CFSG.Quasithin.EmptyFaithful.R3c12Cl

public section

namespace CFSG.Quasithin.R3c10

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Blueprint
open scoped commutatorElement

section Cases

@[expose] def Lemma115LieHighRest3 (X : Type) [Group X] : Prop :=
  (∃ f : ℕ, (2 ≤ f ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSp 2 2 f) ∨
      (2 ≤ f ∧ ChevalleyExceptionalModel X .G2 2 f) ∨
      (1 ≤ f ∧ ChevalleyExceptionalModel X .trialityD4 2 f) ∨
      (Odd f ∧ 3 ≤ f ∧ ReeTitsModel X .twistedF4 2 f)) ∨
    ReeTitsModel X .Tits 2 1

theorem lemma115LieHighRest2_cases_rest3 {X : Type} [Group X] (h : Lemma115LieHighRest2 X) :
    Lemma115LieHighRest3 X ∨ CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 5 2 1 := h

end Cases

section Main

@[expose] def Input15335CloseLieRest3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp2 T Mc M V₁ V₂ Yp I L t →
      (∀ K : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M K → K ≤ I → K = I) →
        I ≤ Subgroup.normalizer (L : Set G) → I = L ⊔ Sgp153 T V₁ → Yp ≤ L →
          Lemma115LieHighRest3 (↥L ⧸ Subgroup.center ↥L) → False

theorem input15335CloseLieRest2_of_rest3 (h113 : StageLemma14113) (kR : Input15335CloseLieRest3) :
    Input15335CloseLieRest2 := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hmin hN hIeq hYL hRest
  rcases lemma115LieHighRest2_cases_rest3 hRest with h3 | h5
  · exact kR G T Mc M V₁ V₂ Yp I L t c hmin hN hIeq hYL h3
  · exact R3c15.l_cl h113 c hN hYL (n := 5) (by norm_num) h5

theorem input15335CloseLieRest_of_rest3 (h113 : StageLemma14113) (kR : Input15335CloseLieRest3) :
    Input15335CloseLieRest :=
  input15335CloseLieRest_of_rest2 h113 (input15335CloseLieRest2_of_rest3 h113 kR)

end Main

end CFSG.Quasithin.R3c10
