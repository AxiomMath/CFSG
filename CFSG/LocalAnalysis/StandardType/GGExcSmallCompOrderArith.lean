module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerTagsBasic

public section

namespace CFSG.StandardType

namespace SmallCompOrder

theorem two_part_cases {q N X n : ℕ} (hq : q = 4 ∨ q = 8) (hX : X % 2 = 1) (h : q ^ N * X = n)
    (hn : n = 174182400 ∨ n = 25920 ∨ n = 360) :
    (q = 4 ∧ N = 6 ∧ n = 174182400) ∨ (q = 4 ∧ N = 3 ∧ n = 25920) ∨
      (q = 8 ∧ N = 4 ∧ n = 174182400) ∨ (q = 8 ∧ N = 2 ∧ n = 25920) ∨
        (q = 8 ∧ N = 1 ∧ n = 360) := by
  have hX1 : 1 ≤ X := by omega
  have hqN : q ^ N ≤ n := by
    calc q ^ N = q ^ N * 1 := (mul_one _).symm
      _ ≤ q ^ N * X := Nat.mul_le_mul_left _ hX1
      _ = n := h
  have hN : N ≤ 13 := by
    by_contra hN
    push Not at hN
    have h4 : 4 ^ 14 ≤ q ^ N :=
      calc 4 ^ 14 ≤ 4 ^ N := Nat.pow_le_pow_right (by norm_num) hN
        _ ≤ q ^ N := Nat.pow_le_pow_left (by rcases hq with rfl | rfl <;> norm_num) N
    norm_num at h4
    rcases hn with rfl | rfl | rfl <;> omega
  rcases hq with rfl | rfl <;> interval_cases N <;> rcases hn with rfl | rfl | rfl <;>
    norm_num at h ⊢ <;> omega

theorem ggNotExcThreeOrder_of_counts {q N d m : ℕ} (c : ℕ → ℕ) (hq : q = 4 ∨ q = 8)
    (hc0 : c 0 = 1) (hsym : ∀ k ≤ N, c (N - k) = c k)
    (hstep : ∀ k, 1 ≤ k → c k ≤ d * c (k - 1)) (hd : d ≤ N)
    (hm : ∀ p : ℕ, p.Prime → p ∣ m → p ∣ q - 1) (hm0 : 0 < m) :
    GGNotExcThreeOrder (m * q ^ N * ∑ k ∈ Finset.range (N + 1), c k * q ^ k) := by
  obtain ⟨P, hP⟩ : ∃ P, P = ∑ k ∈ Finset.range (N + 1), c k * q ^ k := ⟨_, rfl⟩
  rw [← hP]
  have hPmod : P % q = 1 := by
    rw [hP, Finset.sum_range_succ', hc0, pow_zero, mul_one]
    obtain ⟨t, ht⟩ : q ∣ ∑ k ∈ Finset.range N, c (k + 1) * q ^ (k + 1) :=
      Finset.dvd_sum fun k _ => Dvd.dvd.mul_left (dvd_pow_self q (Nat.succ_ne_zero k)) _
    rw [ht]
    rcases hq with rfl | rfl <;> omega
  have hmodd : m % 2 = 1 := by
    by_contra h
    have h2 := hm 2 Nat.prime_two (by omega)
    rcases hq with rfl | rfl <;> norm_num at h2
  have hPodd : P % 2 = 1 := by rcases hq with rfl | rfl <;> omega
  have hX : (m * P) % 2 = 1 := by rw [Nat.mul_mod, hmodd, hPodd]
  have hno : ∀ p : ℕ, p.Prime → p ∣ m → ¬ p ∣ q - 1 → False := fun p hp hpm h => h (hm p hp hpm)
  rw [ggNotExcThreeOrder_iff]
  intro n hn h
  have h' : q ^ N * (m * P) = n := by rw [← h]; ring
  rcases two_part_cases hq hX h' hn with
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  ·
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hP
    norm_num at hP h'
    have h6 : c 6 = c 0 := hsym 0 (by norm_num)
    have h5 : c 5 = c 1 := hsym 1 (by norm_num)
    have h4 : c 4 = c 2 := hsym 2 (by norm_num)
    have hd6 : d ≤ 6 := hd
    have h1 : c 1 ≤ 6 := by
      have := hstep 1 le_rfl
      rw [show 1 - 1 = 0 from rfl, hc0, mul_one] at this
      omega
    have h2 : c 2 ≤ 6 * c 1 := (hstep 2 (by norm_num)).trans (Nat.mul_le_mul_right _ hd6)
    have h3 : c 3 ≤ 6 * c 2 := (hstep 3 (by norm_num)).trans (Nat.mul_le_mul_right _ hd6)
    have hP1 : 4097 ≤ P := by omega
    have hmP : m * P = 42525 := by omega
    have hm10 : m ≤ 10 := by
      have := Nat.mul_le_mul_left m hP1
      omega
    interval_cases m <;> try omega
    all_goals exact hno 5 (by norm_num) (by norm_num) (by norm_num)
  ·
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hP
    norm_num at hP h'
    have h3 : c 3 = c 0 := hsym 0 (by norm_num)
    have h2 : c 2 = c 1 := hsym 1 (by norm_num)
    have h1 : c 1 ≤ 3 := by
      have := hstep 1 le_rfl
      rw [show 1 - 1 = 0 from rfl, hc0, mul_one] at this
      omega
    have hP1 : 65 ≤ P := by omega
    have hmP : m * P = 405 := by omega
    have hm6 : m ≤ 6 := by
      have := Nat.mul_le_mul_left m hP1
      omega
    interval_cases m <;> omega
  ·
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hP
    norm_num at hP h'
    have h4 : c 4 = c 0 := hsym 0 (by norm_num)
    have hP1 : 4097 ≤ P := by omega
    have hmP : m * P = 42525 := by omega
    have hm10 : m ≤ 10 := by
      have := Nat.mul_le_mul_left m hP1
      omega
    interval_cases m <;> try omega
    all_goals exact hno 5 (by norm_num) (by norm_num) (by norm_num)
  ·
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hP
    norm_num at hP h'
    have h2 : c 2 = c 0 := hsym 0 (by norm_num)
    have hP1 : 65 ≤ P := by omega
    have hmP : m * P = 405 := by omega
    have hm6 : m ≤ 6 := by
      have := Nat.mul_le_mul_left m hP1
      omega
    interval_cases m <;> try omega
    all_goals exact hno 5 (by norm_num) (by norm_num) (by norm_num)
  ·
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hP
    norm_num at hP h'
    have h1 : c 1 = c 0 := hsym 0 (by norm_num)
    have hP1 : 9 ≤ P := by omega
    have hmP : m * P = 45 := by omega
    have hm5 : m ≤ 5 := by
      have := Nat.mul_le_mul_left m hP1
      omega
    interval_cases m <;> try omega
    all_goals exact hno 5 (by norm_num) (by norm_num) (by norm_num)

end SmallCompOrder

end CFSG.StandardType
