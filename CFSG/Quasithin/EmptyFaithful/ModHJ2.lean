module

public import CFSG.Quasithin.EmptyFaithful.ModHCl1
public import CFSG.Quasithin.EmptyFaithful.ModHTop6

public section

namespace CFSG.Quasithin.ModH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Blueprint

@[expose] def SylowFactsJ2 : Prop :=
  CenterSmall (NativeSporadic.Carrier .J2) ∧
    ∀ (T : Sylow 2 (NativeSporadic.Carrier .J2)) (α : MulAut (NativeSporadic.Carrier .J2)),
      (∀ t ∈ (T : Subgroup (NativeSporadic.Carrier .J2)), α t = t) →
        ∃ z : (T : Subgroup (NativeSporadic.Carrier .J2)),
          z ∈ Subgroup.center (T : Subgroup (NativeSporadic.Carrier .J2)) ∧
            ∀ g : NativeSporadic.Carrier .J2, α g = (z : NativeSporadic.Carrier .J2) * g *
              (z : NativeSporadic.Carrier .J2)⁻¹

theorem false_of_j2 {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (h113 : StageLemma14113) (hJ : SylowFactsJ2) (c : CtxComp2 T Mc M V₁ V₂ Yp I L t)
    (hN : I ≤ Subgroup.normalizer (L : Set G)) (hYL : Yp ≤ L)
    (e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* NativeSporadic.Carrier .J2) : False := by
  have hZ : centerOf L = CFSG.Open.pCoreOf 2 L := c.c33.center_eq
  have hpc := SBd13.pCore_eq_center_of_center_eq hZ
  exact Cl.false_of_close h113 c hN hYL ((QuotientGroup.quotientMulEquivOfEq hpc.symm).trans e)
    hJ.2 hJ.1

@[expose] def Input15342SporadicNoM11M22M12HSRuM24HeJ2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp2 T Mc M V₁ V₂ Yp I L t →
      (∀ K : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M K → K ≤ I → K = I) →
        I ≤ Subgroup.normalizer (L : Set G) → I = L ⊔ Sgp153 T V₁ → Yp ≤ L →
          (∃ s : TauCeti.SporadicName, IsLemma115SporadicName s ∧ s ≠ .M11 ∧ s ≠ .M22 ∧ s ≠ .M12 ∧
              s ≠ .HS ∧ s ≠ .Ru ∧ s ≠ .M24 ∧ s ≠ .He ∧ s ≠ .J2 ∧
              Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* CFSG.Blueprint.NativeSporadic.Carrier s)) → False

theorem input15342SporadicNoM11M22M12HSRuM24He_of_noJ2 (h113 : StageLemma14113)
    (hJ : SylowFactsJ2) (k : Input15342SporadicNoM11M22M12HSRuM24HeJ2) :
    Input15342SporadicNoM11M22M12HSRuM24He := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hmin hN hIeq hYL hs
  obtain ⟨s, hsn, hne11, hne22, hne12, hneHS, hneRu, hne24, hneHe, ⟨e⟩⟩ := hs
  by_cases hJ2 : s = .J2
  · subst hJ2
    exact false_of_j2 h113 hJ c hN hYL e
  · exact k G T Mc M V₁ V₂ Yp I L t c hmin hN hIeq hYL
      ⟨s, hsn, hne11, hne22, hne12, hneHS, hneRu, hne24, hneHe, hJ2, ⟨e⟩⟩

end CFSG.Quasithin.ModH
