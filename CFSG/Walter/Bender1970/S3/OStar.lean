module

import CFSG.FeitThompson.OddOrderTheorem
import CFSG.GroupTheory.LocalCores.Components
import CFSG.Adapters.GeneralizedFitting
public import CFSG.Walter.Bender1970.S2.OddFitting
public import CFSG.Walter.Bender1970.S2.Subnormal

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter
open scoped commutatorElement

section TypeForm

variable {X : Type*} [Group X] [Finite X]

theorem pPrimeCore_le_centralizer_componentLayerOf :
    pPrimeCore 2 X ≤ Subgroup.centralizer (componentLayerOf (⊤ : Subgroup X) : Set X) := by
  have hodd : Odd (Nat.card (pPrimeCore 2 X)) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hsolv : Group.IsSolvable (pPrimeCore 2 X) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have h := (CFSG.LocalCores.component_solvable_centralizer hsolv
    (inferInstance : (pPrimeCore 2 X).Normal).isSubnormal).2
  rw [componentLayerOf_top_eq_layer]
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at h
  exact h

theorem oStar_inf_centralizer_le_generalizedFitting (hX : IsAStar X) :
    oStar X ⊓ Subgroup.centralizer (CFSG.fittingSubgroup X : Set X) ≤
      generalizedFittingSubgroupOf (⊤ : Subgroup X) := by
  classical
  set O := pPrimeCore 2 X with hO
  set q := QuotientGroup.mk' O with hq
  set E := componentLayerOf (⊤ : Subgroup X) with hE
  set Eb := E.map q with hEb
  have hEn : E.Normal := by
    rw [hE, componentLayerOf_top_eq_layer]
    have := CFSG.LocalCores.layer_characteristic (G := X)
    infer_instance
  have hEbn : Eb.Normal := hEn.map q (QuotientGroup.mk'_surjective O)
  have hEbE : Eb ≤ componentLayerOf (⊤ : Subgroup (X ⧸ O)) := by
    rw [hEb, hE, componentLayerOf, Subgroup.map_le_iff_le_comap]
    refine sSup_le fun K hK => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup (hX.component_image hK).1
  have hFb : generalizedFittingSubgroupOf (⊤ : Subgroup (X ⧸ O)) ≤
      Eb ⊔ Subgroup.centralizer (Eb : Set (X ⧸ O)) := by
    refine sup_le ?_ ?_
    · refine le_sup_of_le_right ?_
      rw [Subgroup.le_centralizer_iff]
      refine hEbE.trans (sSup_le fun K hK => ?_)
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact component_centralizes_fittingSubgroupOf hK
    · refine sSup_le fun K hK => ?_
      rcases isComponentOf_le_or_commutator_eq_bot hK le_top
          (by rw [Subgroup.normalizer_eq_top_iff.mpr hEbn]) with h | h
      · exact le_sup_of_le_left h
      · exact le_sup_of_le_right (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h)
  rintro x ⟨hx, hxF⟩
  have hqx : q x ∈ Eb ⊔ Subgroup.centralizer (Eb : Set (X ⧸ O)) := hFb hx
  obtain ⟨eb, heb, cb, hcb, hebcb⟩ := Subgroup.mem_sup_of_normal_left.mp hqx
  obtain ⟨e, heE, rfl⟩ := heb
  set c := e⁻¹ * x with hc
  have hqc : q c = cb := by
    rw [hc, map_mul, map_inv, ← hebcb]
    group
  have hcE : c ∈ Subgroup.centralizer (E : Set X) := by
    have h1 : ⁅E, Subgroup.zpowers c⁆ ≤ O := by
      rw [Subgroup.commutator_le]
      intro y hy z hz
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      rw [← QuotientGroup.ker_mk' O, MonoidHom.mem_ker, map_commutatorElement, map_zpow, hqc]
      have hcy : cb ^ k ∈ Subgroup.centralizer (Eb : Set (X ⧸ O)) :=
        Subgroup.zpow_mem _ hcb k
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact ((Subgroup.mem_centralizer_iff.mp hcy) (q y) ⟨y, hy, rfl⟩)
    have h2 : ⁅⁅E, Subgroup.zpowers c⁆, E⁆ = ⊥ := by
      refine le_bot_iff.mp ((Subgroup.commutator_mono h1 le_rfl).trans ?_)
      rw [le_bot_iff, Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact pPrimeCore_le_centralizer_componentLayerOf
    have h3 := CFSG.LocalCores.perfect_double_commutator (componentLayerOf_isPerfect _) h2
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h3
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact ((Subgroup.mem_centralizer_iff.mp (h3 hy)) c (Subgroup.mem_zpowers c)).symm
  have hEF : E ≤ Subgroup.centralizer (CFSG.fittingSubgroup X : Set X) := by
    have h := CFSG.LocalCores.fitting_layer_commute (G := X)
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at h
    rw [hE, componentLayerOf_top_eq_layer]
    exact h
  have hcF : c ∈ Subgroup.centralizer (CFSG.fittingSubgroup X : Set X) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (hEF heE)) hxF
  have hcFs : c ∈ generalizedFittingSubgroupOf (⊤ : Subgroup X) := by
    refine CFSG.Adapters.centralizer_generalizedFittingSubgroupOf_top_le ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hle : generalizedFittingSubgroupOf (⊤ : Subgroup X) ≤
        Subgroup.centralizer ({c} : Set X) := by
      refine sup_le ?_ ?_
      · intro f hf
        have hf' : f ∈ CFSG.fittingSubgroup X :=
          CFSG.fittingSubgroupOf_le_fittingSubgroup ⊤ Subgroup.normal_top hf
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp hcF) f hf'
      · intro f hf
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp hcE) f hf
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
  have hx' : x = e * c := by rw [hc]; group
  rw [hx']
  exact Subgroup.mul_mem _ (le_sup_right (a := CFSG.fittingSubgroupOf (⊤ : Subgroup X)) heE) hcFs

end TypeForm

section SubgroupForm

variable {G : Type*} [Group G] [Finite G]

theorem le_generalizedFittingSubgroupOf_of_le_oStar {X K : Subgroup G} (hX : IsAStar X)
    (hKO : K ≤ (oStar X).map X.subtype)
    (hKF : K ≤ Subgroup.centralizer (CFSG.fittingSubgroupOf X : Set G)) :
    K ≤ generalizedFittingSubgroupOf X := by
  intro k hk
  obtain ⟨x, hx, rfl⟩ := hKO hk
  rw [← generalizedFittingSubgroupOf_subgroup_top_eq X]
  refine ⟨x, oStar_inf_centralizer_le_generalizedFitting hX ⟨hx, ?_⟩, rfl⟩
  show x ∈ Subgroup.centralizer (CFSG.fittingSubgroup X : Set X)
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  apply Subtype.ext
  have hy' : (y : G) ∈ CFSG.fittingSubgroupOf X := ⟨y, hy, rfl⟩
  exact (Subgroup.mem_centralizer_iff.mp (hKF hk)) _ hy'

omit [Finite G] in
theorem mem_map_oStar_of_orderOf {X : Subgroup G} (hX : IsAStar X) {t : G} (htX : t ∈ X)
    (ht : orderOf t = 2) : t ∈ (oStar X).map X.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (Subgroup.zpowers (⟨t, htX⟩ : X)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, ht, pow_one])
  exact ⟨⟨t, htX⟩, le_oStar_of_isPGroup hX hp (Subgroup.mem_zpowers _), rfl⟩

omit [Finite G] in
theorem map_oStar_le_normalizer (X : Subgroup G) :
    X ≤ Subgroup.normalizer (((oStar X).map X.subtype : Subgroup G) : Set G) := by
  have hn : (oStar X).Normal := oStar_normal
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨y', hy', rfl⟩
    exact ⟨⟨x, hx⟩ * y' * ⟨x, hx⟩⁻¹, hn.conj_mem y' hy' ⟨x, hx⟩, rfl⟩
  · rintro ⟨y', hy', hy'eq⟩
    refine ⟨⟨x, hx⟩⁻¹ * y' * ⟨x, hx⟩, ?_, ?_⟩
    · have := hn.conj_mem y' hy' ⟨x, hx⟩⁻¹
      simpa using this
    · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hy'eq ⊢
      rw [hy'eq]
      group

theorem mem_normalizer_of_mem_map_oStar {X L : Subgroup G} (hX : IsAStar X)
    (hL : IsComponentOf L X) {t : G} (ht : t ∈ (oStar X).map X.subtype) :
    t ∈ Subgroup.normalizer (L : Set G) := by
  obtain ⟨t', ht', rfl⟩ := ht
  have hN := oStar_le_normalizer hX (fstar_isComponentOf_subgroupOf_top hL) ht'
  rw [Subgroup.mem_normalizer_iff] at hN ⊢
  intro y
  constructor
  · intro hy
    have h1 := (hN ⟨y, hL.1 hy⟩).mp (Subgroup.mem_subgroupOf.mpr hy)
    exact Subgroup.mem_subgroupOf.mp h1
  · intro hy
    have hyX : y ∈ X := by
      have h2 : (t' : G) * y * (t' : G)⁻¹ ∈ X := hL.1 hy
      have h3 : y = (t' : G)⁻¹ * ((t' : G) * y * (t' : G)⁻¹) * t' := by group
      rw [h3]
      exact X.mul_mem (X.mul_mem (X.inv_mem t'.2) h2) t'.2
    have h1 := (hN ⟨y, hyX⟩).mpr (Subgroup.mem_subgroupOf.mpr hy)
    exact Subgroup.mem_subgroupOf.mp h1

theorem mem_normalizer_of_isComponentOf_of_orderOf {X L : Subgroup G} (hX : IsAStar X)
    (hL : IsComponentOf L X) {t : G} (htX : t ∈ X) (ht : orderOf t = 2) :
    t ∈ Subgroup.normalizer (L : Set G) :=
  mem_normalizer_of_mem_map_oStar hX hL (mem_map_oStar_of_orderOf hX htX ht)

end SubgroupForm

end CFSG.Walter
