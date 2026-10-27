module

public import CFSG.Quasithin.EmptyFaithful.ModHTop4
public import CFSG.Quasithin.EmptyFaithful.ModHM24f

public section

namespace CFSG.Quasithin.ModH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Blueprint

@[expose] def Input15342SporadicNoM11M22M12HSRuM24 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp2 T Mc M V₁ V₂ Yp I L t →
      (∀ K : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M K → K ≤ I → K = I) →
        I ≤ Subgroup.normalizer (L : Set G) → I = L ⊔ Sgp153 T V₁ → Yp ≤ L →
          (∃ s : TauCeti.SporadicName, IsLemma115SporadicName s ∧ s ≠ .M11 ∧ s ≠ .M22 ∧ s ≠ .M12 ∧
              s ≠ .HS ∧ s ≠ .Ru ∧ s ≠ .M24 ∧
              Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* CFSG.Blueprint.NativeSporadic.Carrier s)) → False

theorem input15342SporadicNoM11M22M12HSRu_of_noM24
    (k : Input15342SporadicNoM11M22M12HSRuM24) : Input15342SporadicNoM11M22M12HSRu := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hmin hN hIeq hYL hs
  obtain ⟨s, hsn, hne11, hne22, hne12, hneHS, hneRu, ⟨e⟩⟩ := hs
  by_cases h24 : s = .M24
  · subst h24
    exact M24f.false_of_m24 c hmin hN hIeq hYL e
  · exact k G T Mc M V₁ V₂ Yp I L t c hmin hN hIeq hYL
      ⟨s, hsn, hne11, hne22, hne12, hneHS, hneRu, h24, ⟨e⟩⟩

end CFSG.Quasithin.ModH
