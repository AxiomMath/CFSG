module

public import CFSG.RankThree.GF2n.Stroth78.Sec3Comp
public import CFSG.RankThree.GF2n.Stroth78.Sec3Lbar

import CFSG.GroupTheory.OddOrderCardFour
import CFSG.GroupTheory.OddOrderLift
import CFSG.RankThree.GF2n.Stroth78.Sec2SeventeenHyper
import CFSG.RankThree.GF2n.Stroth78.Sec2SeventeenT
import CFSG.RankThree.GF2n.Stroth78.Sec2HyperplaneDual
import CFSG.RankThree.GF2n.Stroth78.Sec4ThreeLift
import CFSG.RankThree.GF2n.Stroth78.Sec4ThreeZQ

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions Module
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem conj_eq_self_of_commutatorElement_mem_ZQ_of_card_ZQ_eq_four (S : Setting z E F)
    (hZ : Nat.card ↥(ZQ z) = 4) {h a : G} (hhH : h ∈ H z) (hodd : Odd (orderOf h))
    (ha : h * a * h⁻¹ * a⁻¹ ∈ ZQ z) : h * a * h⁻¹ = a := by
  have hzV : z ∈ ZQ z := z_mem_ZQ S
  have hz1 : z ≠ 1 := by
    intro h1
    have h2 := S.hyp.orderOf_z
    rw [h1, orderOf_one] at h2
    omega
  have hhz : h * z * h⁻¹ = z := by
    have hc : z * h = h * z := Subgroup.mem_centralizer_iff.mp hhH z (Set.mem_singleton z)
    calc h * z * h⁻¹ = (z * h) * h⁻¹ := by rw [← hc]
      _ = z := by group
  have hhV : ∀ v ∈ ZQ z, h * v * h⁻¹ ∈ ZQ z := by
    intro v hv
    have hv' := (conjAutZQ S ⟨h, hhH⟩ ⟨v, hv⟩).2
    rwa [conjAutZQ_apply] at hv'
  set s : G := h * a * h⁻¹ * a⁻¹ with hs_def
  have hsZ : s ∈ ZQ z := by rwa [hs_def]
  have hs_fix : h * s * h⁻¹ = s :=
    CFSG.GroupTheory.conj_eq_self_of_card_eq_four hZ hhV hzV hz1 hhz hodd hsZ
  have hs2 : s * s = 1 := by
    have := ZQ_mul_self S ⟨s, hsZ⟩
    simpa using congrArg Subtype.val this
  have ht : h * a * h⁻¹ = s * a := by
    rw [hs_def]
    group
  exact CFSG.GroupTheory.conj_eq_self_of_conj_eq_mul_of_odd_orderOf hodd hs_fix hs2 ht

theorem exists_lift_of_odd_order_of_fixes_aVec (S : Setting z E F)
    (hZ : Nat.card ↥(ZQ z) = 4) {a : G} (haQ : a ∈ Q z) {y : Hbar z} {p : ℕ}
    (hoddp : Odd p) (hy : orderOf y = p)
    (hya : rhoLin S y (aVec S haQ) = aVec S haQ) :
    ∃ h : ↥(H z), (QuotientGroup.mk' ((Q z).subgroupOf (H z))) h = y ∧
      Odd (orderOf (h : G)) ∧ orderOf (h : G) = p ∧ (h : G) * a * (h : G)⁻¹ = a := by
  have hyodd : Odd (orderOf y) := by rw [hy]; exact hoddp
  obtain ⟨hH, hfh, hhodd⟩ := CFSG.GroupTheory.exists_odd_orderOf_preimage
    (QuotientGroup.mk' ((Q z).subgroupOf (H z)))
    (QuotientGroup.mk'_surjective ((Q z).subgroupOf (H z))) hyodd
  have hhoddG : Odd (orderOf (hH : G)) := by simpa using hhodd
  have hker : IsPGroup 2 (QuotientGroup.mk' ((Q z).subgroupOf (H z))).ker := by
    rw [QuotientGroup.ker_mk']
    exact IsPGroup.comap_subtype (Q_isPGroup S)
  have hordhH : orderOf hH = p := by
    have hmapord := CFSG.GroupTheory.orderOf_map_eq_of_coprime_of_isPGroup_ker
      (QuotientGroup.mk' ((Q z).subgroupOf (H z))) hker hhodd.coprime_two_right
    rw [hfh, hy] at hmapord
    exact hmapord.symm
  have hordhG : orderOf (hH : G) = p := by
    rw [← Subgroup.orderOf_mk (hH : G) hH.2]
    exact hordhH
  have hfix : rhoLin S ((QuotientGroup.mk' ((Q z).subgroupOf (H z))) hH)
      (aVec S haQ) = aVec S haQ := by
    rw [hfh]
    exact hya
  have hmemZQ : (hH : G) * a * (hH : G)⁻¹ * a⁻¹ ∈ ZQ z :=
    mem_ZQ_of_rhoLin_apply_aVec_eq S haQ hH.2 hfix
  have hha : (hH : G) * a * (hH : G)⁻¹ = a :=
    conj_eq_self_of_commutatorElement_mem_ZQ_of_card_ZQ_eq_four S hZ hH.2 hhoddG hmemZQ
  exact ⟨hH, hfh, hhoddG, hordhG, hha⟩

theorem eq_one_of_odd_mem_centralizer_Lbar_of_card_ZQ_eq_four (S : Setting z E F) {a : G}
    (haQ : a ∈ Q z) (hconj : IsConj z a) (haZ : a ∉ ZQ z) (hza : z ∈ QaOf a)
    (hZ : Nat.card ↥(ZQ z) = 4) {y : Hbar z} (hy : Odd (orderOf y))
    (hyL : y ∈ Subgroup.centralizer (Lbar S a : Set (Hbar z)))
    (hya : rhoLin S y (aVec S haQ) = aVec S haQ) : y = 1 := by
  by_contra hy1
  have hyord1 : orderOf y ≠ 1 := fun h => hy1 (orderOf_eq_one_iff.mp h)
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hyord1
  set y₁ : Hbar z := y ^ (orderOf y / p) with hy1_def
  have hord1 : orderOf y₁ = p := by
    rw [hy1_def]
    exact orderOf_pow_orderOf_div (by have := hy.pos; omega) hpdvd
  have hy1ne : y₁ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hord1
    exact hp.ne_one hord1.symm
  have hoddp : Odd p := hy.of_dvd_nat hpdvd
  have hp2 : p ≠ 2 := by
    rintro rfl
    obtain ⟨j, hj⟩ := hoddp
    omega
  have hy1L : y₁ ∈ Subgroup.centralizer (Lbar S a : Set (Hbar z)) := by
    rw [hy1_def]
    exact Subgroup.pow_mem _ hyL _
  have hpow_apply : ∀ k : ℕ, ((rhoLin S y) ^ k) (aVec S haQ) = aVec S haQ := by
    intro k
    rw [LinearEquiv.coe_pow]
    exact Function.iterate_fixed hya k
  have hya1 : rhoLin S y₁ (aVec S haQ) = aVec S haQ := by
    rw [hy1_def]
    have hrho : rhoLin S (y ^ (orderOf y / p)) = (rhoLin S y) ^ (orderOf y / p) := by
      show (rhoBar S (y ^ (orderOf y / p)) : Additive (QbarOf S) ≃ₗ[ZMod 2]
        Additive (QbarOf S)) = ((rhoBar S y : Additive (QbarOf S) ≃ₗ[ZMod 2]
        Additive (QbarOf S))) ^ (orderOf y / p)
      rw [map_pow, Subgroup.coe_pow]
    rw [hrho]
    exact hpow_apply _
  obtain ⟨hH, hfh, hhoddG, hordhG, hha⟩ :=
    exists_lift_of_odd_order_of_fixes_aVec S hZ haQ hoddp hord1 hya1
  have hres := eq_one_of_odd_prime_power_mem_centralizer_Lbar_of_centralizes_a
    S haQ hconj haZ hza hH.2 hha hp hp2 (k := 1) (by simpa using hordhG) (by
      rw [hfh]
      exact hy1L)
  have hy1bot : y₁ = 1 := by
    rw [← hfh]
    exact hres
  exact hy1ne hy1bot

theorem stroth78_217_of_card_ZQ_eq_four (S : Setting z E F) {a : G}
    (haQ : a ∈ Q z) (hconj : IsConj z a) (haZ : a ∉ ZQ z) (hza : z ∈ QaOf a)
    (hZ : Nat.card ↥(ZQ z) = 4) :
    ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S haQ ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥ := by
  intro Y hO2gen hO2' _hYR hY2 ha_not hL
  by_cases hR : Rbar S a = ⊥
  · exact Or.inl hR
  right
  have hZQa : ¬ centerIn (QaOf a) ≤ Q z :=
    not_centerIn_le_Q_of_Rbar_ne_bot S hza hR
  have hY2' : ∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v : Additive (QbarOf S),
      ((rhoBar S y : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)))
        (((rhoBar S r : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) v - v) =
      ((rhoBar S r : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) v - v := by
    intro y hy r hr v
    exact hY2 y hy r hr _ (sub_mem_commSpace (rhoLin S r) v)
  have ha_not' : Additive.ofMul (mkQbar S ⟨a, haQ⟩) ∉
      Submodule.span (ZMod 2) {u | ∃ y ∈ Y, ∃ v : Additive (QbarOf S),
        u = ((rhoBar S y : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) v - v} := by
    intro hmem
    apply ha_not
    rw [iSup_subtype']
    rwa [← diffSpan_eq_iSup_commSpace]
  have hcommL : ∀ l ∈ Lbar S a, ∀ y ∈ Y, Commute l y :=
    commutator_Lbar_Y_eq_one_of_Rbar_ne_bot S haQ hconj haZ hza Y hO2' hY2' ha_not' hL hR
  have hgen_one : ∀ y ∈ Y, Odd (orderOf y) → y = 1 := by
    intro y hyY hyodd
    have hyL : y ∈ Subgroup.centralizer (Lbar S a : Set (Hbar z)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      exact (hcommL l hl y hyY).eq
    obtain ⟨r, hr1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hR
    have hr1' : (r : Hbar z) ≠ 1 := fun h1 => hr1 (Subtype.ext h1)
    have hmem := aV_mem_commSpace_rhoBar_of_mem_Rbar S haQ hconj haZ hza hZQa r.2 hr1'
    have hya : rhoLin S y (aVec S haQ) = aVec S haQ :=
      hY2 y hyY (r : Hbar z) r.2 (aVec S haQ) (by simpa [aVec, rhoLin] using hmem)
    exact eq_one_of_odd_mem_centralizer_Lbar_of_card_ZQ_eq_four S haQ hconj haZ hza hZ
      hyodd hyL hya
  have hO2gen' : Subgroup.closure {y | y ∈ Y ∧ Odd (orderOf y)} = Y := by
    simpa only [CFSG.GroupTheory.oddOrderClosure_eq_closure] using hO2gen
  have hle : Subgroup.closure {y | y ∈ Y ∧ Odd (orderOf y)} ≤ ⊥ := by
    rw [Subgroup.closure_le]
    rintro y ⟨hyY, hyodd⟩
    simpa using hgen_one y hyY hyodd
  rw [hO2gen'] at hle
  exact le_bot_iff.mp hle

end CFSG.RankThree.GF2n.Stroth78
