module

public import CFSG.Quasithin.EmptyFaithful.SBd13M11
public import CFSG.Quasithin.EmptyFaithful.SBd12M11
public import CFSG.Quasithin.EmptyFaithful.R3c14Red
public import CFSG.Quasithin.EmptyFaithful.R3c9Elim

public section

namespace CFSG.Quasithin.SBd13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Blueprint
  CFSG.Quasithin.R3c14

section Quot

variable {G : Type} [Group G]

theorem center_le_pCore_of_center_eq {L : Subgroup G} (h : centerOf L = pCoreOf 2 L) :
    Subgroup.center ↥L ≤ CFSG.pCore 2 ↥L := by
  intro x hx
  have hx' : (x : G) ∈ centerOf L := SBd11.mem_centerOf_iff_center.2 hx
  rw [h] at hx'
  obtain ⟨y, hy, hyx⟩ := hx'
  have : y = x := Subtype.ext hyx
  exact this ▸ hy

theorem pCore_eq_center_of_center_eq {L : Subgroup G} (h : centerOf L = pCoreOf 2 L) :
    CFSG.pCore 2 ↥L = Subgroup.center ↥L :=
  le_antisymm (SBd12.pCore_le_center_of_center_eq h) (center_le_pCore_of_center_eq h)

end Quot

section Main

variable {G : Type} [Group G] [Finite G]

theorem false_of_not_elConfig {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (c : CtxComp1 T Mc M V₁ V₂ Yp I L t) (o : Concl15343Open T M V₁ V₂ Yp I L)
    (hN : I ≤ Subgroup.normalizer (L : Set G)) (hYL : Yp ≤ L) {X : Type} [Group X]
    (e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* X) (hX : ¬ ElConfig X) : False := by
  have hel := R3c14.elConfig_of_ctx1 c o hN hYL
  have hpc := pCore_eq_center_of_center_eq c.c33.center_eq
  exact hX (ElConfig.map ((QuotientGroup.quotientMulEquivOfEq hpc.symm).trans e) hel)

theorem false_of_m11 {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (c : CtxComp1 T Mc M V₁ V₂ Yp I L t) (o : Concl15343Open T M V₁ V₂ Yp I L)
    (hN : I ≤ Subgroup.normalizer (L : Set G)) (hYL : Yp ≤ L)
    (e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* CFSG.Quasithin.F420.M11G) : False :=
  false_of_not_elConfig c o hN hYL e not_elConfig_m11

@[expose] def Input15343ElimSporadicNoM11 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp1 T Mc M V₁ V₂ Yp I L t → Concl15343Open T M V₁ V₂ Yp I L →
      (∀ K : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M K → K ≤ I → K = I) →
        I ≤ Subgroup.normalizer (L : Set G) → I = L ⊔ Sgp153 T V₁ → Yp ≤ L →
          (∃ s : TauCeti.SporadicName, IsLemma115SporadicName s ∧ s ≠ .M11 ∧
            Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* CFSG.Blueprint.NativeSporadic.Carrier s)) → False

theorem input15343ElimSporadic_of_noM11
    (k : Input15343ElimSporadicNoM11) : R3c9.Input15343ElimSporadic := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c o hmin hN hIeq hYL hs
  obtain ⟨s, hsn, ⟨e⟩⟩ := hs
  by_cases h11 : s = .M11
  · subst h11
    exact false_of_m11 c o hN hYL e
  · exact k G T Mc M V₁ V₂ Yp I L t c o hmin hN hIeq hYL ⟨s, hsn, h11, ⟨e⟩⟩

theorem input15343ElimSporadicNoM11_of_el
    (k : ∀ s : TauCeti.SporadicName, IsLemma115SporadicName s → s ≠ .M11 →
      ¬ ElConfig (CFSG.Blueprint.NativeSporadic.Carrier s)) : Input15343ElimSporadicNoM11 := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c o hmin hN hIeq hYL hs
  obtain ⟨s, hsn, hne, ⟨e⟩⟩ := hs
  exact false_of_not_elConfig c o hN hYL e (k s hsn hne)

end Main

end CFSG.Quasithin.SBd13
