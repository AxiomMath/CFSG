module

public import CFSG.RankThree.GF2n.Tim81.Recog.L2Gen
import CFSG.RankThree.GF2n.Tim81.Sec6.S61Tools

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Timmesfeld.ARS
open scoped MatrixGroups

variable {G : Type} [Group G] {A B : Subgroup G}

theorem IsL2Gen.mem_of_commute (h : IsL2Gen A B) {a z : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    (hz : z ∈ A ⊔ B) (hc : Commute a z) : z ∈ A := by
  obtain ⟨F, hField, hFin, hCharP, φ, hcard, hA, hB⟩ := h
  letI := hField
  letI := hFin
  letI := hCharP
  let aH : ↥(A ⊔ B) := ⟨a, Subgroup.mem_sup_left ha⟩
  let zH : ↥(A ⊔ B) := ⟨z, hz⟩
  have haH : aH ∈ A.subgroupOf (A ⊔ B) := Subgroup.mem_subgroupOf.mpr ha
  have hφa : φ aH ∈ utri F := by
    rw [← hA]
    exact Subgroup.mem_map_of_mem φ.toMonoidHom haH
  obtain ⟨s, hs⟩ := mem_utri_iff.mp hφa
  have hs0 : s ≠ 0 := by
    intro h0
    apply ha1
    have h1 : φ aH = 1 := by rw [hs, h0, utriElt_zero]
    have h2 : aH = 1 := φ.injective (by simpa using h1)
    have h3 : (aH : G) = 1 := congrArg Subtype.val h2
    simpa [aH] using h3
  have hczH : Commute aH zH := Subtype.ext hc.eq
  have hcz : Commute (φ aH) (φ zH) := hczH.map φ.toMonoidHom
  rw [hs] at hcz
  have hzcent : φ zH ∈ Subgroup.centralizer ({utriElt s} : Set (SL(2, F))) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcz.symm.eq
  rw [centralizer_utriElt hs0] at hzcent
  have hzA : zH ∈ A.subgroupOf (A ⊔ B) := by
    have hmem : φ zH ∈ (A.subgroupOf (A ⊔ B)).map φ.toMonoidHom := by
      rw [hA]
      exact hzcent
    have hpre : φ.symm (φ zH) ∈ A.subgroupOf (A ⊔ B) :=
      (Subgroup.mem_map_equiv (f := φ)).1 hmem
    simpa using hpre
  exact Subgroup.mem_subgroupOf.mp hzA

theorem IsL2Gen.not_commute_of_ne_one (h : IsL2Gen A B) {a b : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    (hb : b ∈ B) (hb1 : b ≠ 1) : ¬ Commute a b := by
  intro hc
  have hbA : b ∈ A := h.mem_of_commute ha ha1 (Subgroup.mem_sup_right hb) hc
  have hbBot : b ∈ (⊥ : Subgroup G) := by
    rw [← h.inf_eq_bot]
    exact Subgroup.mem_inf.mpr ⟨hbA, hb⟩
  exact hb1 (Subgroup.mem_bot.mp hbBot)

theorem IsL2Gen.exists_conj_of_ne_one (h : IsL2Gen A B) {a a' : G} (ha : a ∈ A)
    (ha1 : a ≠ 1) (ha' : a' ∈ A) (ha1' : a' ≠ 1) :
    ∃ y ∈ A ⊔ B, y * a * y⁻¹ = a' ∧ y ∈ Subgroup.normalizer (A : Set G) := by
  obtain ⟨F, hField, hFin, hCharP, φ, hcard, hA, hB⟩ := h
  letI := hField
  letI := hFin
  letI := hCharP
  let aH : ↥(A ⊔ B) := ⟨a, Subgroup.mem_sup_left ha⟩
  let aH' : ↥(A ⊔ B) := ⟨a', Subgroup.mem_sup_left ha'⟩
  have haH : aH ∈ A.subgroupOf (A ⊔ B) := Subgroup.mem_subgroupOf.mpr ha
  have haH' : aH' ∈ A.subgroupOf (A ⊔ B) := Subgroup.mem_subgroupOf.mpr ha'
  have hφa : φ aH ∈ utri F := by
    rw [← hA]
    exact Subgroup.mem_map_of_mem φ.toMonoidHom haH
  have hφa' : φ aH' ∈ utri F := by
    rw [← hA]
    exact Subgroup.mem_map_of_mem φ.toMonoidHom haH'
  obtain ⟨s, hs⟩ := mem_utri_iff.mp hφa
  obtain ⟨t, ht⟩ := mem_utri_iff.mp hφa'
  have hs0 : s ≠ 0 := by
    intro h0
    apply ha1
    have h1 : φ aH = 1 := by rw [hs, h0, utriElt_zero]
    have h2 : aH = 1 := φ.injective (by simpa using h1)
    have h3 : (aH : G) = 1 := congrArg Subtype.val h2
    simpa [aH] using h3
  have ht0 : t ≠ 0 := by
    intro h0
    apply ha1'
    have h1 : φ aH' = 1 := by rw [ht, h0, utriElt_zero]
    have h2 : aH' = 1 := φ.injective (by simpa using h1)
    have h3 : (aH' : G) = 1 := congrArg Subtype.val h2
    simpa [aH'] using h3
  obtain ⟨b, hb, hbconj⟩ := exists_mem_borel_conj_utriElt hs0 ht0
  have hbN : b ∈ Subgroup.normalizer (utri F : Set (SL(2, F))) := by
    rw [normalizer_utri]
    exact hb
  let yH : ↥(A ⊔ B) := φ.symm b
  have hyN : yH ∈ Subgroup.normalizer ((A.subgroupOf (A ⊔ B) : Subgroup ↥(A ⊔ B)) :
      Set ↥(A ⊔ B)) := by
    have hmapN := Subgroup.map_equiv_normalizer_eq (A.subgroupOf (A ⊔ B)) φ
    have hbmem : b ∈ (Subgroup.normalizer ((A.subgroupOf (A ⊔ B) : Subgroup ↥(A ⊔ B)) :
        Set ↥(A ⊔ B))).map φ.toMonoidHom := by
      rw [hmapN, hA]
      exact hbN
    have hpre := (Subgroup.mem_map_equiv (f := φ) (K := Subgroup.normalizer
      ((A.subgroupOf (A ⊔ B) : Subgroup ↥(A ⊔ B)) : Set ↥(A ⊔ B)))).1 hbmem
    simpa [yH] using hpre
  have hyφ : φ yH = b := φ.apply_symm_apply b
  have hconjH : yH * aH * yH⁻¹ = aH' := by
    apply φ.injective
    rw [map_mul, map_mul, map_inv, hs, ht, hyφ, hbconj]
  have hconjG : (yH : G) * a * (yH : G)⁻¹ = a' := by
    simpa using congrArg Subtype.val hconjH
  have hyNG : (yH : G) ∈ Subgroup.normalizer (A : Set G) := by
    have hWH : conjSubgroup yH (A.subgroupOf (A ⊔ B)) = A.subgroupOf (A ⊔ B) := by
      simpa [conjSubgroup] using Subgroup.mem_normalizer_iff_map_conj_eq.mp hyN
    have hmap := congrArg (Subgroup.map (A ⊔ B).subtype) hWH
    rw [map_conjSubgroup, Subgroup.map_subgroupOf_eq_of_le (le_sup_left : A ≤ A ⊔ B)] at hmap
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (by simpa [conjSubgroup] using hmap)
  exact ⟨(yH : G), yH.2, hconjG, hyNG⟩

theorem IsL2Gen.not_isPGroup (h : IsL2Gen A B) : ¬ IsPGroup 2 ↥(A ⊔ B) := by
  intro h2
  obtain ⟨a, ha, b, hb, hab⟩ := h.exists_orderOf_eq_three
  have hab' : a * b ∈ A ⊔ B :=
    (A ⊔ B).mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp h2) ⟨a * b, hab'⟩
  rw [Subgroup.orderOf_mk (H := A ⊔ B) (a := a * b) (ha := hab'), hab] at hk
  have hdvd : 3 ∣ 2 ^ k := by rw [← hk]
  exact absurd (Nat.prime_three.dvd_of_dvd_pow hdvd) (by norm_num)

end CFSG.RankThree.GF2n.Tim81
