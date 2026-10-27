module

public import CFSG.Quasithin.EmptyFaithful.ModHJ4Cfg
public import CFSG.Quasithin.EmptyFaithful.ModHJ4Odd
public import CFSG.Quasithin.EmptyFaithful.ModHJ2
public import CFSG.Quasithin.EmptyFaithful.A38c8J4

public section

namespace CFSG.Quasithin.ModH.J4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem false_of_j4
    (hF2 : FactJ4TwoLocals2)
    {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (c : CtxComp2 T Mc M V₁ V₂ Yp I L t)
    (hmin : ∀ K : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M K → K ≤ I → K = I)
    (hN : I ≤ Subgroup.normalizer (L : Set G)) (hIeq : I = L ⊔ Sgp153 T V₁) (hYL : Yp ≤ L)
    (e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* NativeSporadic.Carrier .J4) : False := by
  have hZ : centerOf L = CFSG.Open.pCoreOf 2 L := c.c33.center_eq
  have hpc := SBd13.pCore_eq_center_of_center_eq hZ
  let qe : (↥L ⧸ Subgroup.center ↥L) ≃* NativeSporadic.Carrier .J4 :=
    (QuotientGroup.quotientMulEquivOfEq hpc.symm).trans e
  have hcen : Subgroup.center (↥L ⧸ Subgroup.center ↥L) = ⊥ := center_quot_eq_bot c
  have hcfg := config2_of_ctx c hmin hN hcen hIeq hYL
  have hs0 : IsSimpleGroup (NativeSporadic.Carrier .J4) := CFSG.Sporadic.J4.fam_j4_simplicity.2.2
  have hsimple : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := qe.isSimpleGroup
  have hodd : Odd (Nat.card (Outer (↥L ⧸ Subgroup.center ↥L))) :=
    A38c8.odd_card_outer_of_isSporadic_j4 ⟨qe⟩
  have hA : ∀ α ∈ {α | ∃ (s : G) (hs : s ∈ Sgp153 T V₁), α = actQ hN ⟨s, sgp153_le c hs⟩},
      ∃ q ∈ img (rho0 hN hcen) (Sgp153 T V₁), α = MulAut.conj q := by
    rintro α ⟨s, hs, rfl⟩
    have hS2 : IsPGroup 2 ↥(Sgp153 T V₁) := c.facts.sylow.2.1
    set P : Subgroup (MulAut (↥L ⧸ Subgroup.center ↥L)) :=
      ((Sgp153 T V₁).subgroupOf I).map (actQ hN) with hPdef
    have hP2 : IsPGroup 2 ↥P := (isPGroup_subgroupOf hS2).map (actQ hN)
    have hPin : P ≤ inner (↥L ⧸ Subgroup.center ↥L) :=
      A38c8.le_inner_of_isPGroup_two_odd hodd P hP2
    have hmem : actQ hN ⟨s, sgp153_le c hs⟩ ∈ P :=
      ⟨⟨s, sgp153_le c hs⟩, Subgroup.mem_subgroupOf.2 hs, rfl⟩
    obtain ⟨q, hq⟩ := hPin hmem
    have hsin : s ∈ innerPart hN := mem_innerPart.2 ⟨sgp153_le c hs, q, hq⟩
    exact ⟨rho0 hN hcen ⟨s, hsin⟩, mem_img.2 ⟨s, hsin, hs, rfl⟩,
      (conj_rho0 hN hcen ⟨s, hsin⟩).symm⟩
  exact false_of_config2_inner hF2 ⟨qe⟩ hsimple hcfg hA (solvableOverSylow_j4 _ ⟨qe⟩ _ hcfg.sylow)

end CFSG.Quasithin.ModH.J4

namespace CFSG.Quasithin.ModH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Blueprint

@[expose] def Input15342SporadicNoM11M22M12HSRuM24HeJ2J4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp2 T Mc M V₁ V₂ Yp I L t →
      (∀ K : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M K → K ≤ I → K = I) →
        I ≤ Subgroup.normalizer (L : Set G) → I = L ⊔ Sgp153 T V₁ → Yp ≤ L →
          (∃ s : TauCeti.SporadicName, IsLemma115SporadicName s ∧ s ≠ .M11 ∧ s ≠ .M22 ∧ s ≠ .M12 ∧
              s ≠ .HS ∧ s ≠ .Ru ∧ s ≠ .M24 ∧ s ≠ .He ∧ s ≠ .J2 ∧ s ≠ .J4 ∧
              Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* CFSG.Blueprint.NativeSporadic.Carrier s)) → False

theorem input15342SporadicNoM11M22M12HSRuM24HeJ2_of_noJ4
    (hF2 : FactJ4TwoLocals2)
    (k : Input15342SporadicNoM11M22M12HSRuM24HeJ2J4) : Input15342SporadicNoM11M22M12HSRuM24HeJ2 := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hmin hN hIeq hYL hs
  obtain ⟨s, hsn, hne11, hne22, hne12, hneHS, hneRu, hne24, hneHe, hneJ2, ⟨e⟩⟩ := hs
  by_cases hJ4 : s = .J4
  · subst hJ4
    exact J4.false_of_j4 hF2 c hmin hN hIeq hYL e
  · exact k G T Mc M V₁ V₂ Yp I L t c hmin hN hIeq hYL
      ⟨s, hsn, hne11, hne22, hne12, hneHS, hneRu, hne24, hneHe, hneJ2, hJ4, ⟨e⟩⟩

end CFSG.Quasithin.ModH
