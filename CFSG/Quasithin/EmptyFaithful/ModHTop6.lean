module

public import CFSG.Quasithin.EmptyFaithful.ModHTop5
public import CFSG.Quasithin.EmptyFaithful.ModHHe3

public section

namespace CFSG.Quasithin.ModH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Blueprint

@[expose] def Input15342SporadicNoM11M22M12HSRuM24He : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp2 T Mc M V₁ V₂ Yp I L t →
      (∀ K : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M K → K ≤ I → K = I) →
        I ≤ Subgroup.normalizer (L : Set G) → I = L ⊔ Sgp153 T V₁ → Yp ≤ L →
          (∃ s : TauCeti.SporadicName, IsLemma115SporadicName s ∧ s ≠ .M11 ∧ s ≠ .M22 ∧ s ≠ .M12 ∧
              s ≠ .HS ∧ s ≠ .Ru ∧ s ≠ .M24 ∧ s ≠ .He ∧
              Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* CFSG.Blueprint.NativeSporadic.Carrier s)) → False

theorem input15342SporadicNoM11M22M12HSRuM24_of_noHe
    (k : Input15342SporadicNoM11M22M12HSRuM24He) : Input15342SporadicNoM11M22M12HSRuM24 := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hmin hN hIeq hYL hs
  obtain ⟨s, hsn, hne11, hne22, hne12, hneHS, hneRu, hne24, ⟨e⟩⟩ := hs
  by_cases hHe : s = .He
  · subst hHe
    exact He3.false_of_he c hmin hN hIeq hYL e
  · exact k G T Mc M V₁ V₂ Yp I L t c hmin hN hIeq hYL
      ⟨s, hsn, hne11, hne22, hne12, hneHS, hneRu, hne24, hHe, ⟨e⟩⟩

end CFSG.Quasithin.ModH
