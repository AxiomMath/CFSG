module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Vol2.Ch10SecFAct

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Equiv

variable {G : Type} [Group G]

theorem map_one_of_mul {N : Subgroup G} {π : G → Perm (Fin 5)}
    (hπ : ∀ y ∈ N, ∀ z ∈ N, π (y * z) = π y * π z) : π 1 = 1 := by
  have h := hπ 1 N.one_mem 1 N.one_mem
  rw [mul_one] at h
  exact left_eq_mul.mp h

theorem map_pow_of_mul {N : Subgroup G} {π : G → Perm (Fin 5)}
    (hπ : ∀ y ∈ N, ∀ z ∈ N, π (y * z) = π y * π z) {y : G} (hy : y ∈ N) (n : ℕ) :
    π (y ^ n) = π y ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, map_one_of_mul hπ]
  | succ n ih => rw [pow_succ, hπ _ (N.pow_mem hy n) _ hy, ih, pow_succ]

theorem map_inv_of_mul {N : Subgroup G} {π : G → Perm (Fin 5)}
    (hπ : ∀ y ∈ N, ∀ z ∈ N, π (y * z) = π y * π z) {y : G} (hy : y ∈ N) :
    π y⁻¹ = (π y)⁻¹ := by
  have h := hπ y hy y⁻¹ (N.inv_mem hy)
  rw [mul_inv_cancel, map_one_of_mul hπ] at h
  exact eq_inv_of_mul_eq_one_right h.symm

variable [Finite G]

omit [Finite G] in
theorem orderOf_mk_eq_three {Y C : Subgroup G} (hidx : C.relIndex Y = 3)
    [(C.subgroupOf Y).Normal] {p : G} (hpY : p ∈ Y) (hpC : p ∉ C) :
    orderOf (QuotientGroup.mk (⟨p, hpY⟩ : ↥Y) : ↥Y ⧸ C.subgroupOf Y) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card (↥Y ⧸ C.subgroupOf Y) = 3 := hidx
  have hne : (QuotientGroup.mk (⟨p, hpY⟩ : ↥Y) : ↥Y ⧸ C.subgroupOf Y) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff]
    exact fun h => hpC (Subgroup.mem_subgroupOf.mp h)
  refine orderOf_eq_prime ?_ hne
  rw [← hcard]
  exact pow_card_eq_one'

omit [Finite G] in
theorem exists_pow_inv_mul_mem {Y C : Subgroup G} (hidx : C.relIndex Y = 3)
    [(C.subgroupOf Y).Normal] {p : G} (hpY : p ∈ Y) (hpC : p ∉ C) {x : G} (hxY : x ∈ Y) :
    ∃ j : ℕ, j < 3 ∧ (p ^ j)⁻¹ * x ∈ C := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card (↥Y ⧸ C.subgroupOf Y) = 3 := hidx
  have ho := orderOf_mk_eq_three hidx hpY hpC
  have hne : (QuotientGroup.mk (⟨p, hpY⟩ : ↥Y) : ↥Y ⧸ C.subgroupOf Y) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ho
    omega
  have htop := zpowers_eq_top_of_prime_card hcard hne
  have hxm : (QuotientGroup.mk (⟨x, hxY⟩ : ↥Y) : ↥Y ⧸ C.subgroupOf Y) ∈
      Subgroup.zpowers (QuotientGroup.mk (⟨p, hpY⟩ : ↥Y)) := htop ▸ Subgroup.mem_top _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxm
  refine ⟨(k % 3).toNat, by omega, ?_⟩
  have hk' : (QuotientGroup.mk (⟨p, hpY⟩ : ↥Y) : ↥Y ⧸ C.subgroupOf Y) ^ (k % 3).toNat =
      QuotientGroup.mk (⟨x, hxY⟩ : ↥Y) := by
    have h3 : (3 : ℤ) = ((orderOf (QuotientGroup.mk (⟨p, hpY⟩ : ↥Y) :
        ↥Y ⧸ C.subgroupOf Y) : ℕ) : ℤ) := by rw [ho]; norm_num
    rw [← hk, ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg k (by norm_num)), h3,
      zpow_mod_orderOf]
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq] at hk'
  exact Subgroup.mem_subgroupOf.mp hk'

theorem exists_three_part {Y C : Subgroup G} (hidx : C.relIndex Y = 3)
    [(C.subgroupOf Y).Normal] {y : G} (hyY : y ∈ Y) (hyC : y ∉ C) :
    ∃ p ∈ Y, p ∉ C ∧ ∃ a : ℕ, p ^ 3 ^ a = 1 := by
  obtain ⟨a, b, hb3, hk⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos y).ne' 3 (by norm_num)
  refine ⟨y ^ b, Y.pow_mem hyY b, fun hpC => hb3 ?_, a, ?_⟩
  · have ho := orderOf_mk_eq_three hidx hyY hyC
    rw [← ho]
    apply orderOf_dvd_of_pow_eq_one
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr hpC
  · rw [← pow_mul, mul_comm, ← hk, pow_orderOf_eq_one]

end CFSG.Quasithin.Vol2.Ch10.SecF
