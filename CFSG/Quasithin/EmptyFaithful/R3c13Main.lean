module

public import CFSG.Quasithin.EmptyFaithful.R3c13El
public import CFSG.Quasithin.EmptyFaithful.R3c13A6
public import CFSG.Quasithin.EmptyFaithful.R3c13L3
public import CFSG.Quasithin.EmptyFaithful.R3c11Core

public section

namespace CFSG.Quasithin.R3c10

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Blueprint
open CFSG.Quasithin.R3c13
open scoped commutatorElement

section Cases

@[expose] def Lemma115LieRest2 (X : Type) [Group X] : Prop :=
  (((∃ f : ℕ, (2 ≤ f ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSp 2 2 f) ∨
      (2 ≤ f ∧ ChevalleyExceptionalModel X .G2 2 f) ∨
      (1 ≤ f ∧ ChevalleyExceptionalModel X .trialityD4 2 f) ∨
      (Odd f ∧ 3 ≤ f ∧ ReeTitsModel X .twistedF4 2 f)) ∨
    ReeTitsModel X .Tits 2 1) ∨
    (∃ n : ℕ, (n = 4 ∨ n = 5) ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL n 2 1)) ∨
  CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSU 3 3 1

theorem lemma115LieRest_cases_rest2 {X : Type} [Group X] (h : Lemma115LieRest X) :
    Lemma115LieRest2 X ∨ CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 3 2 1 ∨
      Nonempty (X ≃* alternatingGroup (Fin 6)) := by
  rcases h with (((⟨f, hfam⟩ | hTits) | hL45) | ⟨⟨e⟩⟩ | hU33)
  · rcases hfam with ⟨hf, hm⟩ | h2 | h3 | h4 | h5
    · subst hf
      exact Or.inr (Or.inl hm)
    · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨f, Or.inl h2⟩)))
    · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨f, Or.inr (Or.inl h3)⟩)))
    · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨f, Or.inr (Or.inr (Or.inl h4))⟩)))
    · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨f, Or.inr (Or.inr (Or.inr h5))⟩)))
  · exact Or.inl (Or.inl (Or.inl (Or.inr hTits)))
  · exact Or.inl (Or.inl (Or.inr hL45))
  · exact Or.inr (Or.inr ⟨e⟩)
  · exact Or.inl (Or.inr hU33)

end Cases

section Main

@[expose] def Input15343ElimLieRest2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp1 T Mc M V₁ V₂ Yp I L t → Concl15343Open T M V₁ V₂ Yp I L →
      (∀ K : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M K → K ≤ I → K = I) →
        I ≤ Subgroup.normalizer (L : Set G) → I = L ⊔ Sgp153 T V₁ → Yp ≤ L →
          Lemma115LieRest2 (↥L ⧸ Subgroup.center ↥L) → False

theorem input15343ElimLieRest_of_rest2 (kR : Input15343ElimLieRest2) : Input15343ElimLieRest := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c o hmin hN hIeq hYL hRest
  rcases lemma115LieRest_cases_rest2 hRest with h2 | h3 | ⟨⟨φ⟩⟩
  · exact kR G T Mc M V₁ V₂ Yp I L t c o hmin hN hIeq hYL h2
  · exact el_a4 c o hN hYL (kleinSelfCent_of_psl3 h3).sylow
  · exact el_a4 c o hN hYL (sylowKleinSelfCent_of_alt6 φ)

end Main

end CFSG.Quasithin.R3c10
