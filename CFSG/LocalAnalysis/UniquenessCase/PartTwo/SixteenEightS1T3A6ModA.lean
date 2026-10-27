module

public import CFSG.Walter.W67.W1Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup

theorem s16t3_a6mod_exists_mul_of_mem_sup_of_commute {G : Type*} [Group G] {H K : Subgroup G}
    (hcomm : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) {x : G} (hx : x ∈ H ⊔ K) :
    ∃ h ∈ H, ∃ k ∈ K, h * k = x := by
  have h := (CFSG.Walter.W67.card_sup_mul_card_inf_of_commute H K hcomm).2
  have hx' : x ∈ ((H ⊔ K : Subgroup G) : Set G) := hx
  rw [h] at hx'
  obtain ⟨h, hh, k, hk, hk'⟩ := hx'
  exact ⟨h, hh, k, hk, hk'⟩

theorem s16t3_a6mod_normal_of_sup_of_commute {G : Type*} [Group G] {N K A : Subgroup G}
    (hNA : N ≤ A) (hNK : N ⊔ K = A)
    (hcomm : ∀ n ∈ N, ∀ k ∈ K, n * k = k * n) : (N.subgroupOf A).Normal := by
  rw [Subgroup.normal_subgroupOf_iff hNA]
  intro x a hx ha
  have ha' : a ∈ N ⊔ K := by rw [hNK]; exact ha
  obtain ⟨n, hn, k, hk, rfl⟩ := s16t3_a6mod_exists_mul_of_mem_sup_of_commute hcomm ha'
  have hkx : k * x * k⁻¹ = x := by
    rw [← hcomm x hx k hk, mul_assoc, mul_inv_cancel, mul_one]
  have hconj : (n * k) * x * (n * k)⁻¹ = n * x * n⁻¹ := by
    rw [mul_inv_rev]
    calc n * k * x * (k⁻¹ * n⁻¹) = n * (k * x * k⁻¹) * n⁻¹ := by group
      _ = n * x * n⁻¹ := by rw [hkx]
  rw [hconj]
  exact N.mul_mem (N.mul_mem hn hx) (N.inv_mem hn)

theorem s16t3_a6mod_mem_of_odd_order_of_relIndex_le_two {G : Type*} [Group G] [Finite G]
    {L N : Subgroup G} (hLN : (L.subgroupOf N).Normal) (h : L.relIndex N ≤ 2)
    {x : G} (hxN : x ∈ N) (hx : Odd (orderOf x)) : x ∈ L := by
  set x' : ↥N := ⟨x, hxN⟩ with hx'
  set q : ↥N ⧸ L.subgroupOf N := QuotientGroup.mk' (L.subgroupOf N) x' with hq
  have hq_dvd : orderOf q ∣ L.relIndex N := by
    rw [Subgroup.relIndex]
    exact orderOf_dvd_natCard q
  have hq2 : orderOf q ∣ 2 := by
    have hpos : 0 < L.relIndex N := by
      rw [Subgroup.relIndex]
      exact Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    rcases (by omega : L.relIndex N = 1 ∨ L.relIndex N = 2) with h1 | h2
    · rw [h1] at hq_dvd
      exact Nat.dvd_one.mp hq_dvd ▸ one_dvd 2
    · rwa [h2] at hq_dvd
  have hqx : orderOf q ∣ orderOf x := by
    apply orderOf_dvd_of_pow_eq_one
    have hx'ord : (x' : ↥N) ^ orderOf x = 1 := by
      rw [← show orderOf (x' : ↥N) = orderOf x from (Subgroup.orderOf_coe x').symm]
      exact pow_orderOf_eq_one _
    calc q ^ orderOf x = QuotientGroup.mk' (L.subgroupOf N) ((x' : ↥N) ^ orderOf x) := by
          rw [hq, ← map_pow]
      _ = 1 := by rw [hx'ord, map_one]
  have hq1 : orderOf q = 1 := by
    have hcop : Nat.Coprime 2 (orderOf x) := hx.coprime_two_left
    have hd := Nat.dvd_gcd hq2 hqx
    rw [hcop.gcd_eq_one] at hd
    exact Nat.dvd_one.mp hd
  exact Subgroup.mem_subgroupOf.mp
    ((QuotientGroup.eq_one_iff x').mp (orderOf_eq_one_iff.mp hq1))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
