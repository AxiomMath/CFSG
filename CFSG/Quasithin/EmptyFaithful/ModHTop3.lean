module

public import CFSG.Quasithin.EmptyFaithful.ModHM12d
public import CFSG.Quasithin.EmptyFaithful.ModHTop2

public section

namespace CFSG.Quasithin.ModH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Blueprint

@[expose] def Input15342SporadicNoM11M22M12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp2 T Mc M V₁ V₂ Yp I L t →
      (∀ K : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M K → K ≤ I → K = I) →
        I ≤ Subgroup.normalizer (L : Set G) → I = L ⊔ Sgp153 T V₁ → Yp ≤ L →
          (∃ s : TauCeti.SporadicName, IsLemma115SporadicName s ∧ s ≠ .M11 ∧ s ≠ .M22 ∧ s ≠ .M12 ∧
              Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* CFSG.Blueprint.NativeSporadic.Carrier s)) → False

theorem input15342SporadicNoM11M22_of_noM12
    (k : Input15342SporadicNoM11M22M12) : Input15342SporadicNoM11M22 := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hmin hN hIeq hYL hs
  obtain ⟨s, hsn, hne11, hne22, ⟨e⟩⟩ := hs
  by_cases h12 : s = .M12
  · subst h12
    have hX : SolvNine (NativeSporadic.Carrier .M12) := R12.solvNine_M12
    exact false_of_solvNine c hN hYL e hX
  · exact k G T Mc M V₁ V₂ Yp I L t c hmin hN hIeq hYL ⟨s, hsn, hne11, hne22, h12, ⟨e⟩⟩

end CFSG.Quasithin.ModH
