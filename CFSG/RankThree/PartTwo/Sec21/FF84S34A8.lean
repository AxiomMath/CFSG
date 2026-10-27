module

public import CFSG.RankThree.PartTwo.Sec21.FF84S34Dec

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84

open Equiv Equiv.Perm Subgroup CFSG.LocalAnalysis.GLTheoremA.CatB

theorem eq_one_of_cube_sq {H : Type*} [Group H] {p : H} (h3 : p ^ 3 = 1) (h2 : p * p = 1) :
    p = 1 := by
  calc p = p ^ 3 * (p * p)⁻¹ := by group
    _ = 1 := by rw [h3, h2]; simp

theorem closure_pair_eq_P0 {x y : A8} (hx : x ∈ a8P0) (hy : y ∈ a8P0) (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) (hyx : y ∉ zpowers x) : closure ({x, y} : Set A8) = a8P0 := by
  have hle : closure ({x, y} : Set A8) ≤ a8P0 := by
    rw [closure_le]
    intro z hz
    rcases hz with rfl | hz
    · exact hx
    · rw [Set.mem_singleton_iff.1 hz]; exact hy
  have hz3 : Nat.card (zpowers x) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hx3 hx1]
  have hzle : zpowers x ≤ closure ({x, y} : Set A8) :=
    zpowers_le.2 (subset_closure (by simp))
  have hd1 : 3 ∣ Nat.card (closure ({x, y} : Set A8)) := by
    have := card_dvd_of_le hzle
    rwa [hz3] at this
  have hd2 : Nat.card (closure ({x, y} : Set A8)) ∣ 9 := by
    have := card_dvd_of_le hle
    rwa [a8P0_card] at this
  have hne : Nat.card (closure ({x, y} : Set A8)) ≠ 3 := by
    intro h
    have heq : zpowers x = closure ({x, y} : Set A8) :=
      eq_of_le_of_card_ge hzle (by rw [h, hz3])
    exact hyx (heq ▸ subset_closure (by simp))
  have hle9 : Nat.card (closure ({x, y} : Set A8)) ≤ 9 := Nat.le_of_dvd (by norm_num) hd2
  have h9 : Nat.card (closure ({x, y} : Set A8)) = 9 := by
    generalize Nat.card (closure ({x, y} : Set A8)) = c at *
    interval_cases c <;> omega
  exact eq_of_le_of_card_ge hle (by rw [h9, a8P0_card])

theorem pow8_of_two_pow (z : Perm (Fin 8)) {n : ℕ} (h : z ^ (2 ^ n) = 1) : z ^ 8 = 1 := by
  have h1 : orderOf z ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one h
  rw [← orderOf_dvd_iff_pow_eq_one, ← Equiv.Perm.lcm_cycleType]
  refine Multiset.lcm_dvd.2 fun c hc => ?_
  have hcd : c ∣ 2 ^ n := (Equiv.Perm.dvd_of_mem_cycleType hc).trans h1
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hcd
  have hle : c ≤ 8 := by
    have := Equiv.Perm.le_card_support_of_mem_cycleType hc
    have h2 : (Equiv.Perm.support z).card ≤ 8 := by
      simpa using Finset.card_le_univ (Equiv.Perm.support z)
    omega
  have hk3 : k ≤ 3 := by
    by_contra hk4
    have : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rw [hk]
  exact pow_dvd_pow 2 hk3

theorem comm_a8t_of_mem_P0 {p : A8} (hp : p ∈ a8P0) : Commute (p : Perm (Fin 8)) a8t := by
  unfold a8P0 at hp
  induction hp using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact Equiv.ext (by decide)
    · rw [Set.mem_singleton_iff.1 hx]; exact Equiv.ext (by decide)
  | one => exact Commute.one_left _
  | mul x y _ _ hx hy => exact hx.mul_left hy
  | inv x _ hx => exact hx.inv_left

theorem a8c_comm_a8t : Commute a8c a8t := Equiv.ext (by decide)

theorem a8d_comm_a8t : Commute a8d a8t := Equiv.ext (by decide)

theorem a8t_sq : a8t * a8t = 1 := by
  rw [a8t, swap_mul_self]

theorem a8t_ne_one : a8t ≠ 1 := by
  intro h
  have := sign_a8t
  rw [h, sign_one] at this
  exact absurd this (by decide)

theorem mem_P0_of_comm {z : A8} (hc : (z : Perm (Fin 8)) * a8c = a8c * (z : Perm (Fin 8)))
    (hd : (z : Perm (Fin 8)) * a8d = a8d * (z : Perm (Fin 8))) : z ∈ a8P0 := by
  obtain ⟨i, -, j, -, h | h⟩ := centralizer_P0 z hc hd
  · have : z = a8c8 ^ i * a8d8 ^ j := Subtype.ext h
    rw [this]
    exact mul_mem (pow_mem a8c8_mem_P0 _) (pow_mem a8d8_mem_P0 _)
  · exfalso
    have hs : sign (z : Perm (Fin 8)) = 1 := (mem_alternatingGroup.1 z.2)
    have hs2 : sign (a8c ^ i * a8d ^ j) = 1 := by
      have := (mem_alternatingGroup.1 (mul_mem (pow_mem a8c8.2 i) (pow_mem a8d8.2 j)))
      exact this
    rw [h, sign_mul, hs2, one_mul, sign_a8t] at hs
    exact absurd hs (by decide)

theorem eq_one_or_eq_a8t_of_comm {z : Perm (Fin 8)} (hc : z * a8c = a8c * z)
    (hd : z * a8d = a8d * z) (h2 : z * z = 1) : z = 1 ∨ z = a8t := by
  have hcd : Commute a8c a8d := Equiv.ext (by decide)
  obtain ⟨i, -, j, -, h | h⟩ := centralizer_P0 z hc hd
  · left
    have hp3 : (a8c ^ i * a8d ^ j) ^ 3 = 1 := by
      rw [((hcd.pow_left i).pow_right j).mul_pow, ← pow_mul, mul_comm i 3, pow_mul, a8c_cube,
        one_pow, ← pow_mul, mul_comm j 3, pow_mul, a8d_cube, one_pow, one_mul]
    rw [h] at h2 ⊢
    exact eq_one_of_cube_sq hp3 h2
  · right
    have hpt : Commute (a8c ^ i * a8d ^ j) a8t :=
      ((a8c_comm_a8t.pow_left i).mul_left (a8d_comm_a8t.pow_left j))
    have hp3 : (a8c ^ i * a8d ^ j) ^ 3 = 1 := by
      rw [((hcd.pow_left i).pow_right j).mul_pow, ← pow_mul, mul_comm i 3, pow_mul, a8c_cube,
        one_pow, ← pow_mul, mul_comm j 3, pow_mul, a8d_cube, one_pow, one_mul]
    have hsq : (a8c ^ i * a8d ^ j) * (a8c ^ i * a8d ^ j) = 1 := by
      rw [h] at h2
      generalize a8c ^ i * a8d ^ j = p at hpt h2 ⊢
      calc p * p = p * p * (a8t * a8t) := by rw [a8t_sq, mul_one]
        _ = p * (p * a8t) * a8t := by group
        _ = p * (a8t * p) * a8t := by rw [hpt.eq]
        _ = (p * a8t) * (p * a8t) := by group
        _ = 1 := h2
    have hp1 : a8c ^ i * a8d ^ j = 1 := eq_one_of_cube_sq hp3 hsq
    rw [h, hp1, one_mul]

end CFSG.RankThree.PartTwo.Sec21.FF84
