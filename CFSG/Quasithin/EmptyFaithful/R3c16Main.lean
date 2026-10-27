module

public import CFSG.Quasithin.EmptyFaithful.R3c14Rest
public import CFSG.Quasithin.EmptyFaithful.R3c16Tits

public section

namespace CFSG.Quasithin.R3c16

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Blueprint
open CFSG.Quasithin.R3c10
open scoped commutatorElement

section Cases

@[expose] def Lemma115LieRest5 (X : Type) [Group X] : Prop :=
  ∃ f : ℕ, (2 ≤ f ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSp 2 2 f) ∨
      (2 ≤ f ∧ ChevalleyExceptionalModel X .G2 2 f) ∨
      (1 ≤ f ∧ ChevalleyExceptionalModel X .trialityD4 2 f) ∨
      (Odd f ∧ 3 ≤ f ∧ ReeTitsModel X .twistedF4 2 f)

theorem lemma115LieRest4_cases_rest5 {X : Type} [Group X] (h : Lemma115LieRest4 X) :
    Lemma115LieRest5 X ∨ ReeTitsModel X .Tits 2 1 := h

end Cases

section Main

@[expose] def Input15343ElimLieRest5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp1 T Mc M V₁ V₂ Yp I L t → Concl15343Open T M V₁ V₂ Yp I L →
      (∀ K : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M K → K ≤ I → K = I) →
        I ≤ Subgroup.normalizer (L : Set G) → I = L ⊔ Sgp153 T V₁ → Yp ≤ L →
          Lemma115LieRest5 (↥L ⧸ Subgroup.center ↥L) → False

theorem input15343ElimLieRest4_of_rest5
    (kR : Input15343ElimLieRest5) : Input15343ElimLieRest4 := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c o hmin hN hIeq hYL hRest
  rcases lemma115LieRest4_cases_rest5 hRest with h5 | hT
  · exact kR G T Mc M V₁ V₂ Yp I L t c o hmin hN hIeq hYL h5
  · exact not_elConfig_of_tits hT (R3c14.elConfig_of_ctx1 c o hN hYL)

theorem input15343ElimLieRest_of_rest5
    (kR : Input15343ElimLieRest5) : Input15343ElimLieRest :=
  input15343ElimLieRest_of_rest4 (input15343ElimLieRest4_of_rest5 kR)

end Main

end CFSG.Quasithin.R3c16
