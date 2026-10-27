module

public import CFSG.Quasithin.EmptyFaithful.ModHTop3
public import CFSG.Quasithin.EmptyFaithful.ModHHS
public import CFSG.Quasithin.EmptyFaithful.ModHRu

public section

namespace CFSG.Quasithin.ModH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Blueprint

@[expose] def Input15342SporadicNoM11M22M12HSRu : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp2 T Mc M V₁ V₂ Yp I L t →
      (∀ K : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M K → K ≤ I → K = I) →
        I ≤ Subgroup.normalizer (L : Set G) → I = L ⊔ Sgp153 T V₁ → Yp ≤ L →
          (∃ s : TauCeti.SporadicName, IsLemma115SporadicName s ∧ s ≠ .M11 ∧ s ≠ .M22 ∧ s ≠ .M12 ∧
              s ≠ .HS ∧ s ≠ .Ru ∧
              Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* CFSG.Blueprint.NativeSporadic.Carrier s)) → False

theorem input15342SporadicNoM11M22M12_of_noHSRu
    (k : Input15342SporadicNoM11M22M12HSRu) : Input15342SporadicNoM11M22M12 := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hmin hN hIeq hYL hs
  obtain ⟨s, hsn, hne11, hne22, hne12, ⟨e⟩⟩ := hs
  by_cases hHS : s = .HS
  · subst hHS
    exact false_of_solvNineNS c hN hYL e solvNineNS_HS
  by_cases hRu : s = .Ru
  · subst hRu
    exact false_of_solvNineNS c hN hYL e solvNineNS_Ru
  exact k G T Mc M V₁ V₂ Yp I L t c hmin hN hIeq hYL ⟨s, hsn, hne11, hne22, hne12, hHS, hRu, ⟨e⟩⟩

end CFSG.Quasithin.ModH
