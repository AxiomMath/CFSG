module

public import CFSG.RankThree.GF2n.Tim81.Sec6.M0Basic
import CFSG.GroupTheory.InvariantSubgroup
import CFSG.LocalAnalysis.SeitzReduction.F4PilotNonsplitSL2
import CFSG.RankThree.GF2n.Tim81.Sec6.S65
public import CFSG.RankThree.GF2n.Tim81.Sec6.Basic

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim78
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {M V : Subgroup G} {n f : ℕ}

theorem IsL2Gen.exists_orderOf_eq_card_add_one {A B : Subgroup G} (h : IsL2Gen A B) :
    ∃ x ∈ A ⊔ B, orderOf x = Nat.card A + 1 := by
  obtain ⟨F, hField, hFin, hCharP, φ, hcard, -, -⟩ := h
  letI := hField
  letI := hFin
  letI := hCharP
  obtain ⟨t, ht⟩ := CFSG.SeitzReduction.F4Pilot.exists_orderOf_eq_natCard_add_one (K := F)
  refine ⟨((φ.symm t : ↥(A ⊔ B)) : G), (φ.symm t).2, ?_⟩
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq φ.symm t, ht, hcard]

theorem IsL2Gen.inf_cenOf_eq_bot {A B : Subgroup G} (h : IsL2Gen A B) : A ⊓ cenOf B = ⊥ := by
  refine le_bot_iff.mp ?_
  rintro x hx
  obtain ⟨hxA, hxC⟩ := Subgroup.mem_inf.mp hx
  by_contra hx1
  obtain ⟨b, hbB, hnb⟩ := h.exists_not_commute hxA hx1
  exact hnb (Subgroup.mem_centralizer_iff.mp hxC b hbB).symm

theorem exists_l2Datum {A B : Subgroup G} (hA : A ∈ sigmaSet M V) (hB : B ∈ sigmaSet M V)
    (hAB : IsL2Gen A B) : ∃ h : G, L2Datum M V A B h := by
  obtain ⟨g, rfl, hH⟩ := hA
  obtain ⟨x, hx, hord⟩ := hAB.exists_orderOf_eq_card_add_one
  exact ⟨x, ⟨g, rfl, hH⟩, hB, hAB, hx, by rw [hord, card_conjSubgroup]⟩

theorem imgQ_conjSubgroup (y : ↥M) (D : Subgroup G) :
    imgQ M (conjSubgroup (y : G) D) =
      conjSubgroup (QuotientGroup.mk' (pCore 2 ↥M) y) (imgQ M D) := by
  have hsub : (conjSubgroup (y : G) D).subgroupOf M = conjSubgroup y (D.subgroupOf M) := by
    ext m
    rw [Subgroup.mem_subgroupOf, mem_conjSubgroup, mem_conjSubgroup, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [imgQ, hsub, ← CFSG.GroupTheory.map_conjSubgroup (QuotientGroup.mk' (pCore 2 ↥M))
    (D.subgroupOf M) y, imgQ]

theorem Sec6Hyp.imgQ_sup_Pc (hS : Sec6Hyp M V) {Y : Subgroup G} (hY : Y ≤ M) :
    imgQ M (Y ⊔ Pc M V) = imgQ M Y := by
  have himgP : imgQ M (Pc M V) = ⊥ := by
    rw [eq_bot_iff]
    rintro z hz
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hz
    rw [Subgroup.mem_bot, Sec6Hyp.mk_eq_one_iff hS]
    exact Subgroup.mem_subgroupOf.mp hx
  rw [imgQ, Subgroup.subgroupOf_sup hY (hS.sec5.toRootHyp.toHyp.Pc_le_M), Subgroup.map_sup,
    show Subgroup.map (QuotientGroup.mk' (pCore 2 ↥M)) ((Pc M V).subgroupOf M) = ⊥ from himgP,
    sup_bot_eq]

theorem Sec6Hyp.le_sup_Pc_of_imgQ_le (hS : Sec6Hyp M V) {U U' : Subgroup G} (hU : U ≤ M)
    (h : imgQ M U ≤ imgQ M U') : U ≤ U' ⊔ Pc M V := by
  intro u hu
  have huM : u ∈ M := hU hu
  have hmem : QuotientGroup.mk' (pCore 2 ↥M) (⟨u, huM⟩ : ↥M) ∈ imgQ M U := mk_mem_imgQ hu
  obtain ⟨x, hxU', hx⟩ := mem_imgQ_iff.mp (h hmem)
  have hxp : QuotientGroup.mk' (pCore 2 ↥M) (x⁻¹ * ⟨u, huM⟩) = 1 := by
    rw [map_mul, map_inv, hx, inv_mul_cancel]
  have hP : ((x⁻¹ * ⟨u, huM⟩ : ↥M) : G) ∈ Pc M V := (Sec6Hyp.mk_eq_one_iff hS _).mp hxp
  have hxu : u = (x : G) * ((x⁻¹ * ⟨u, huM⟩ : ↥M) : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [hxu]
  exact (U' ⊔ Pc M V).mul_mem (Subgroup.mem_sup_left hxU') (Subgroup.mem_sup_right hP)

theorem Sec5Hyp.card_conj_Pc (hS : Sec5Hyp M V) {U : Subgroup G} (hU : U ∈ sigmaSet M V) :
    Nat.card {U' : Subgroup G // ∃ p ∈ Pc M V, U' = conjSubgroup p U} = Nat.card V ^ 2 := by
  classical
  letI : MulAction ↥(Pc M V) (Subgroup G) :=
    MulAction.compHom (Subgroup G) (MulAut.conj.comp (Pc M V).subtype)
  rw [← hS.card_orbit_Pc hU]
  refine Nat.card_congr
    { toFun := fun U' => ⟨U'.1, by
        obtain ⟨p, hp, hEq⟩ := U'.2
        exact ⟨⟨p, hp⟩, hEq.symm⟩⟩
      invFun := fun X => ⟨X.1, by
        obtain ⟨p, hp⟩ := X.2
        exact ⟨p.1, p.2, hp.symm⟩⟩
      left_inv := fun U' => Subtype.ext rfl
      right_inv := fun X => Subtype.ext rfl }

private theorem card_fiber_imgQ (hS : Sec6Hyp M V) {U₀ : Subgroup G} (hU₀ : U₀ ∈ sigmaSet M V) :
    Nat.card {U : ↥(sigmaSet M V) // imgQ M U.1 = imgQ M U₀} = Nat.card V ^ 2 := by
  classical
  have hne : ∀ {U : Subgroup G}, U ∈ sigmaSet M V → U ≠ ⊥ := by
    intro U hU hbot
    obtain ⟨g, rfl, -⟩ := hU
    have hcard : Nat.card (conjSubgroup g V) = Nat.card V := card_conjSubgroup g V
    rw [hbot, Subgroup.card_bot] at hcard
    have h4 := hS.sec5.toRootHyp.four_le_card
    omega
  have hmem : ∀ p ∈ Pc M V, conjSubgroup p U₀ ∈ sigmaSet M V := fun p hp =>
    hS.sec5.conj_mem_sigmaSet (hS.sec5.toRootHyp.toHyp.Pc_le_M hp) hU₀
  have himg : ∀ p ∈ Pc M V, imgQ M (conjSubgroup p U₀) = imgQ M U₀ := by
    intro p hp
    have hpM : p ∈ M := hS.sec5.toRootHyp.toHyp.Pc_le_M hp
    rw [imgQ_conjSubgroup (⟨p, hpM⟩ : ↥M) U₀,
      show QuotientGroup.mk' (pCore 2 ↥M) (⟨p, hpM⟩ : ↥M) = 1 from
        (Sec6Hyp.mk_eq_one_iff hS _).mpr hp,
      conjSubgroup_one]
  have hkey : ∀ U : ↥(sigmaSet M V), imgQ M U.1 = imgQ M U₀ →
      ∃ p ∈ Pc M V, U.1 = conjSubgroup p U₀ := by
    intro U hU
    have hUM : U.1 ≤ M := (hS.sec5.le_M_of_mem_sigmaSet U.2).1
    have hle : U.1 ≤ U₀ ⊔ Pc M V := hS.le_sup_Pc_of_imgQ_le hUM (by rw [hU])
    have hne' : U.1 ⊓ (U₀ ⊔ Pc M V) ≠ ⊥ := by
      rw [inf_eq_left.mpr hle]
      exact hne U.2
    exact hS.res.s55 M V hS.sec5 U₀ hU₀ U.1 U.2 hne'
  refine (Nat.card_congr
    { toFun := fun U => ⟨U.1.1, hkey U.1 U.2⟩
      invFun := fun U' => ⟨⟨U'.1, by
        obtain ⟨p, hp, hEq⟩ := U'.2
        rw [hEq]
        exact hmem p hp⟩, by
        obtain ⟨p, hp, hEq⟩ := U'.2
        rw [hEq]
        exact himg p hp⟩
      left_inv := fun U => Subtype.ext (Subtype.ext rfl)
      right_inv := fun U' => Subtype.ext rfl }).trans (hS.sec5.card_conj_Pc hU₀)

theorem Sec6Hyp.card_sigmaSet (hS : Sec6Hyp M V) :
    Nat.card (sigmaSet M V) = Nat.card V ^ 2 * Nat.card (imgQ M '' sigmaSet M V) := by
  classical
  let F : ↥(sigmaSet M V) → ↥(imgQ M '' sigmaSet M V) := fun U =>
    ⟨imgQ M U.1, ⟨U.1, U.2, rfl⟩⟩
  have hfib : ∀ z : ↥(imgQ M '' sigmaSet M V),
      Nat.card {U : ↥(sigmaSet M V) // F U = z} = Nat.card V ^ 2 := by
    rintro ⟨z, U₀, hU₀, rfl⟩
    have hiff : ∀ U : ↥(sigmaSet M V), F U = ⟨imgQ M U₀, ⟨U₀, hU₀, rfl⟩⟩ ↔
        imgQ M U.1 = imgQ M U₀ := by
      intro U
      simp only [Subtype.ext_iff, F]
    rw [Nat.card_congr (Equiv.subtypeEquivRight hiff)]
    exact card_fiber_imgQ hS hU₀
  have hmain : Nat.card ↥(sigmaSet M V) =
      Nat.card ↥(imgQ M '' sigmaSet M V) * Nat.card V ^ 2 := by
    haveI : Fintype ↥(imgQ M '' sigmaSet M V) := Fintype.ofFinite _
    rw [Nat.card_congr (Equiv.sigmaFiberEquiv F).symm, Nat.card_sigma]
    simp only [hfib, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]
  rw [hmain, mul_comm]

end CFSG.RankThree.GF2n.Tim81
