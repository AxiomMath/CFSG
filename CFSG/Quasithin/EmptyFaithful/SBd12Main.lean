module

public import CFSG.Quasithin.EmptyFaithful.SBd11Main
public import CFSG.Quasithin.EmptyFaithful.SBd12M11

public section

namespace CFSG.Quasithin.SBd12

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Blueprint
  CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def Input15342SporadicNoM11 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp2 T Mc M V₁ V₂ Yp I L t →
      (∀ K : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M K → K ≤ I → K = I) →
        I ≤ Subgroup.normalizer (L : Set G) → I = L ⊔ Sgp153 T V₁ → Yp ≤ L →
          (∃ s : TauCeti.SporadicName, IsLemma115SporadicName s ∧ s ≠ .M11 ∧
              Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* CFSG.Blueprint.NativeSporadic.Carrier s)) → False

theorem input15342Sporadic_of_noM11 (k : Input15342SporadicNoM11) :
    SBd11.Input15342Sporadic := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hmin hN hIeq hYL hs
  obtain ⟨s, hsn, ⟨e⟩⟩ := hs
  by_cases h11 : s = .M11
  · subst h11
    exact false_of_m11 c hYL e
  · exact k G T Mc M V₁ V₂ Yp I L t c hmin hN hIeq hYL ⟨s, hsn, h11, ⟨e⟩⟩

end CFSG.Quasithin.SBd12
