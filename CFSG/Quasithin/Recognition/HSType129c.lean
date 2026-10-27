module

public import CFSG.Quasithin.Recognition.HSType129a
public import CFSG.Quasithin.Recognition.HSTypeL12f

public section

namespace CFSG.Quasithin.HSType

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type*} [Group G]

abbrev hsD (z d : G) : Subgroup G := hsZQ z ⊔ Subgroup.zpowers d

namespace HSSetting

variable {z : G} {V : Subgroup G}

section D

variable [Finite G] (h : HSSetting z V) {x d : G} (hxH : x ∈ hsH z) (hx3 : orderOf x = 3)
  (hdH : d ∈ hsH z) (hdK : d ∉ hsK z) (hd2 : d * d = 1) (hdx : d * x = x * d)

omit [Finite G] in
include hdK hd2 in
theorem orderOf_d : orderOf d = 2 := by
  refine orderOf_eq_prime (by rw [sq]; exact hd2) fun h1 => hdK ?_
  rw [h1]
  exact (hsK z).one_mem

omit [Finite G] in
include h hdH hdK hd2 in
theorem card_hsD : Nat.card (hsD z d) = 8 := by
  have hdN : Subgroup.zpowers d ≤ Subgroup.normalizer (hsZQ z : Set G) :=
    (Subgroup.zpowers_le).mpr (h.H_le_normalizer_ZQ hdH)
  have hinf : Subgroup.zpowers d ⊓ hsZQ z = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun y ⟨hy, hyZ⟩ => ?_
    rcases eq_one_or_eq_of_mem_zpowers (orderOf_d hdK hd2) hy with rfl | rfl
    · rfl
    · exact absurd (h.Q_le_K hyZ.1) hdK
  have hp := card_sup_mul_card_inf_of_le_normalizer hdN
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, orderOf_d hdK hd2,
    h.card_ZQ, sup_comm] at hp
  exact hp

include h hxH hx3 hdH hdx in
theorem hsD_le : hsD z d ≤ hsH z ⊓ Subgroup.centralizer ({x} : Set G) := by
  refine sup_le ?_ ((Subgroup.zpowers_le).mpr ⟨hdH, ?_⟩)
  · rw [← h.centralizer_Q_eq_ZQ_of_orderOf_three hxH hx3]
    exact le_inf (inf_le_left.trans h.Q_le_H) inf_le_right
  · exact Subgroup.mem_centralizer_singleton_iff.mpr hdx

include h hdH hdK hd2 in
theorem sq_eq_one_or_z_of_mem_hsD {y : G} (hy : y ∈ hsD z d) : y * y = 1 ∨ y * y = z := by
  have hy' : y ∈ Subgroup.zpowers d ⊔ hsZQ z := by
    rw [sup_comm]
    exact hy
  obtain ⟨k, u, hu, rfl⟩ := mem_sup_zpowers (h.H_le_normalizer_ZQ hdH) hy'
  rcases eq_one_or_eq_of_mem_zpowers (orderOf_d hdK hd2)
      (Subgroup.zpow_mem_zpowers d k) with hk | hk
  · rw [hk, one_mul]
    exact h.mul_self_eq_one_or_z hu.1
  · left
    have hinv := h.inv_of_not_mem_K hdH hdK hu
    rw [hk]
    calc d * u * (d * u) = (d * u * d⁻¹) * (d * d) * u := by group
      _ = 1 := by rw [hinv, hd2, mul_one, inv_mul_cancel]

include h hdH hdK hd2 in
theorem conj_z_of_normalizes_hsD {n : G} (hn : n ∈ Subgroup.normalizer (hsD z d : Set G)) :
    n * z * n⁻¹ = z := by
  obtain ⟨w, hwZ, -, -, hww⟩ := h.exists_mem_ZQ_ne
  have hwD : w ∈ hsD z d := Subgroup.mem_sup_left hwZ
  have hnw := (Subgroup.mem_normalizer_iff.mp hn w).mp hwD
  rcases h.sq_eq_one_or_z_of_mem_hsD hdH hdK hd2 hnw with h1 | h1
  · exfalso
    apply h.z_ne_one
    calc z = n⁻¹ * (n * w * n⁻¹ * (n * w * n⁻¹)) * n := by rw [← hww]; group
      _ = 1 := by rw [h1]; group
  · calc n * z * n⁻¹ = n * w * n⁻¹ * (n * w * n⁻¹) := by rw [← hww]; group
      _ = z := h1

include h hxH hx3 in
theorem card_le_of_two_subgroup {P : Subgroup G} (hP : IsPGroup 2 P)
    (hPC : P ≤ hsH z ⊓ Subgroup.centralizer ({x} : Set G)) : Nat.card P ≤ 8 := by
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hdvd := Subgroup.card_dvd_of_le hPC
  rw [h.card_centralizer_H_three hxH hx3, hk] at hdvd
  have h8 : 2 ^ k ∣ 2 ^ 3 := by
    have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
    exact hcop.dvd_of_dvd_mul_right (by norm_num at hdvd ⊢; exact hdvd)
  rw [hk]
  exact Nat.le_of_dvd (by norm_num) h8

include h hxH hx3 hdH hdK hd2 hdx in
theorem eq_hsD_of_le {P : Subgroup G} (hP : IsPGroup 2 P) (hDP : hsD z d ≤ P)
    (hPx : P ≤ Subgroup.centralizer ({x} : Set G)) : P = hsD z d := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have hlt : (hsD z d).subgroupOf P < ⊤ := by
    refine lt_of_le_of_ne le_top fun he => hne ?_
    refine le_antisymm (fun y hy => ?_) hDP
    have : (⟨y, hy⟩ : ↥P) ∈ (hsD z d).subgroupOf P := he ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this
  have : Group.IsNilpotent ↥P := hP.isNilpotent
  have hnc := Group.normalizerCondition_of_isNilpotent (G := ↥P) _ hlt
  obtain ⟨n, hnN, hnD⟩ := IsConcreteLE.exists_of_lt hnc
  have hnN' : (n : G) ∈ Subgroup.normalizer (hsD z d : Set G) := by
    refine Subgroup.mem_normalizer_iff.mpr fun y => ⟨fun hy => ?_, fun hy => ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp hnN ⟨y, hDP hy⟩).mp
        (Subgroup.mem_subgroupOf.mpr hy)
      exact Subgroup.mem_subgroupOf.mp this
    · have hyP : y ∈ P := by
        have := P.mul_mem (P.mul_mem (P.inv_mem n.2) (hDP hy)) n.2
        rwa [show (n : G)⁻¹ * ((n : G) * y * (n : G)⁻¹) * n = y by group] at this
      have := (Subgroup.mem_normalizer_iff.mp hnN ⟨y, hyP⟩).mpr
        (Subgroup.mem_subgroupOf.mpr hy)
      exact Subgroup.mem_subgroupOf.mp this
  have hnH : (n : G) ∈ hsH z := by
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have := h.conj_z_of_normalizes_hsD hdH hdK hd2 hnN'
    calc (n : G) * z = (n : G) * z * (n : G)⁻¹ * (n : G) := by group
      _ = z * (n : G) := by rw [this]
  have hPH : P ⊓ hsH z ≤ hsH z ⊓ Subgroup.centralizer ({x} : Set G) :=
    fun y hy => ⟨hy.2, hPx hy.1⟩
  have hcard := h.card_le_of_two_subgroup hxH hx3 (hP.to_le inf_le_left) hPH
  have hDle : hsD z d ≤ P ⊓ hsH z := le_inf hDP (by
    have := h.hsD_le hxH hx3 hdH hdx
    exact this.trans inf_le_left)
  have heq : hsD z d = P ⊓ hsH z :=
    Subgroup.eq_of_le_of_card_ge hDle (by rw [h.card_hsD hdH hdK hd2]; exact hcard)
  apply hnD
  rw [Subgroup.mem_subgroupOf, heq]
  exact ⟨n.2, hnH⟩

end D

end HSSetting

end CFSG.Quasithin.HSType
