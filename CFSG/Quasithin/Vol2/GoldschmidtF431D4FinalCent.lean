module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4YAmalgam

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin

theorem orderOf_two_pow_of_mul_self {G : Type*} [Group G] {s : G} (hs : s * s = 1) :
    ∃ k : ℕ, orderOf s = 2 ^ k := by
  have h : orderOf s ∣ 2 ^ 1 := orderOf_dvd_of_pow_eq_one (by rw [pow_one, pow_two]; exact hs)
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h
  exact ⟨k, hk⟩

section TwoElements


theorem d4U_orderOf {u : D} (hu : u ∈ d4U) : ∃ k : ℕ, orderOf u = 2 ^ k := by
  have h1 : orderOf (⟨u, hu⟩ : ↥d4U) ∣ Nat.card d4U := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, card_d4U'] at h1
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (show orderOf u ∣ 2 ^ 12 from h1)
  exact ⟨k, hk⟩

variable (hs : IsSimpleGroup D)

include hs in
theorem eq_d4z_of_comm_U {P : Subgroup D} (hP : d4U ≤ P) {n : D} (hn : n ≠ 1)
    (hc : ∀ s : D, (∀ x, x ∈ P ↔ s * x * s⁻¹ ∈ P) → (∃ k : ℕ, orderOf s = 2 ^ k) →
      n * s = s * n) : n = d4z := by
  rcases centralizer_d4U hs (fun u hu => hc u
    (Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer (hP hu))) (d4U_orderOf hu)) with h | h
  · exact absurd h hn
  · exact h

include hs in
theorem d4_swap_false {n : D} (hn : n ≠ 1)
    (hc : ∀ s : D, (∀ x, x ∈ d4N ↔ s * x * s⁻¹ ∈ d4N) → (∃ k : ℕ, orderOf s = 2 ^ k) →
      n * s = s * n) : False := by
  have hnz : n = d4z := eq_d4z_of_comm_U hs (d4U_le_d4B.trans inf_le_right) hn hc
  have hcomm := hc (d4GenG 7) (Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer g7_mem_N))
    (orderOf_two_pow_of_mul_self (d4GenG_sq (by norm_num)))
  rw [hnz] at hcomm
  exact g7_not_mem_H (Subgroup.mem_centralizer_singleton_iff.2 hcomm.symm)

end TwoElements

end CFSG.Quasithin.D4Hex
