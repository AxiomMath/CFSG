module

public import CFSG.Quasithin.EmptyFaithful.R3c14Main
public import CFSG.Quasithin.EmptyFaithful.R3c14Lin

public section

namespace CFSG.Quasithin.R3c10

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Blueprint
open scoped commutatorElement

section Cases

@[expose] def Lemma115LieRest4 (X : Type) [Group X] : Prop :=
  (∃ f : ℕ, (2 ≤ f ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSp 2 2 f) ∨
      (2 ≤ f ∧ ChevalleyExceptionalModel X .G2 2 f) ∨
      (1 ≤ f ∧ ChevalleyExceptionalModel X .trialityD4 2 f) ∨
      (Odd f ∧ 3 ≤ f ∧ ReeTitsModel X .twistedF4 2 f)) ∨
    ReeTitsModel X .Tits 2 1

theorem lemma115LieRest3_cases_rest4 {X : Type} [Group X] (h : Lemma115LieRest3 X) :
    Lemma115LieRest4 X ∨ ∃ n : ℕ, (n = 4 ∨ n = 5) ∧
      CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL n 2 1 := by
  rcases h with hA | hL
  · exact Or.inl hA
  · exact Or.inr hL

end Cases

section Main

@[expose] def Input15343ElimLieRest4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp1 T Mc M V₁ V₂ Yp I L t → Concl15343Open T M V₁ V₂ Yp I L →
      (∀ K : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M K → K ≤ I → K = I) →
        I ≤ Subgroup.normalizer (L : Set G) → I = L ⊔ Sgp153 T V₁ → Yp ≤ L →
          Lemma115LieRest4 (↥L ⧸ Subgroup.center ↥L) → False

theorem input15343ElimLieRest3_of_rest4 (kR : Input15343ElimLieRest4) : Input15343ElimLieRest3 := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c o hmin hN hIeq hYL hRest
  rcases lemma115LieRest3_cases_rest4 hRest with h4 | ⟨n, hn, hL⟩
  · exact kR G T Mc M V₁ V₂ Yp I L t c o hmin hN hIeq hYL h4
  · have hn3 : 3 ≤ n := by omega
    exact R3c14.not_elConfig_of_psl hn3 hL (R3c14.elConfig_of_ctx1 c o hN hYL)

theorem input15343ElimLieRest_of_rest4
    (kR : Input15343ElimLieRest4) : Input15343ElimLieRest :=
  input15343ElimLieRest_of_rest3 (input15343ElimLieRest3_of_rest4 kR)

end Main

end CFSG.Quasithin.R3c10
