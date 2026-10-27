module

public import CFSG.Quasithin.EmptyFaithful.R3c10K42
public import CFSG.Quasithin.EmptyFaithful.SBd11L33

public section

namespace CFSG.Quasithin.SBd11

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Blueprint
  CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def Input15342Sporadic : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp2 T Mc M V₁ V₂ Yp I L t →
      (∀ K : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M K → K ≤ I → K = I) →
        I ≤ Subgroup.normalizer (L : Set G) → I = L ⊔ Sgp153 T V₁ → Yp ≤ L →
          (∃ s : TauCeti.SporadicName, IsLemma115SporadicName s ∧
              Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* CFSG.Blueprint.NativeSporadic.Carrier s)) → False

theorem input15342Residue_of_sporadic (k : Input15342Sporadic) : R3c10.Input15342Residue := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hmin hN hIeq hYL hcases
  rcases hcases with h7 | h33 | hsp
  · obtain ⟨e⟩ := h7
    exact false_of_alt7 c hYL e
  · exact false_of_l33 c hYL h33
  · exact k G T Mc M V₁ V₂ Yp I L t c hmin hN hIeq hYL hsp

end CFSG.Quasithin.SBd11
