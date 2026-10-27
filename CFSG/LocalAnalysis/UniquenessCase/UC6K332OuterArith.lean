module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route

open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator)

theorem lieOrderNumerator_psl (n x : ℕ) :
    lieOrderNumerator .PSL n x = x ^ (n * (n - 1) / 2) * ∏ i ∈ Finset.Icc 2 n, (x ^ i - 1) :=
  rfl

theorem lieOrderNumerator_psu (n x : ℕ) :
    lieOrderNumerator .PSU n x = x ^ (n * (n - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 n, if Even i then x ^ i - 1 else x ^ i + 1 :=
  rfl

theorem three_mul_prod_dvd_of_two {n : ℕ} (hn : 2 ≤ n) {a b : ℕ → ℕ}
    (hab : ∀ i ∈ Finset.Icc 2 n, a i ∣ b i) (h2 : 3 * a 2 ∣ b 2) :
    3 * ∏ i ∈ Finset.Icc 2 n, a i ∣ ∏ i ∈ Finset.Icc 2 n, b i := by
  have hmem : 2 ∈ Finset.Icc 2 n := Finset.mem_Icc.2 ⟨le_rfl, hn⟩
  rw [← Finset.mul_prod_erase _ a hmem, ← Finset.mul_prod_erase _ b hmem, ← mul_assoc]
  exact mul_dvd_mul h2 (Finset.prod_dvd_prod_of_dvd _ _ fun i hi =>
    hab i (Finset.mem_of_mem_erase hi))

theorem three_mul_sub_one_dvd_cube {x : ℕ} (hx : ¬ 3 ∣ x) :
    3 * (x ^ 2 - 1) ∣ (x ^ 3) ^ 2 - 1 := by
  have hx1 : 1 ≤ x := Nat.pos_of_ne_zero fun h => hx (h ▸ dvd_zero 3)
  obtain ⟨y, hy⟩ : ∃ y, y = x ^ 2 := ⟨_, rfl⟩
  have hy1 : 1 ≤ y := hy ▸ Nat.one_le_pow _ _ hx1
  have hy3 : y % 3 = 1 := by
    rw [hy, Nat.pow_mod]
    rcases (show x % 3 = 1 ∨ x % 3 = 2 by omega) with h | h <;> rw [h]
  have e6 : (x ^ 3) ^ 2 = y ^ 3 := by rw [hy, ← pow_mul, ← pow_mul]
  rw [e6, ← hy]
  obtain ⟨c, hc⟩ : 3 ∣ y ^ 2 + y + 1 := by
    have h2 : y ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hy3]
    omega
  have e1 : y ^ 3 - 1 = (y - 1) * (y ^ 2 + y + 1) := by
    have h : 1 ≤ y ^ 3 := Nat.one_le_pow _ _ hy1
    zify [hy1, h]
    ring
  exact ⟨c, by rw [e1, hc]; ring⟩

theorem three_mul_pow_mul_dvd {x m P Q : ℕ} (hm : 1 ≤ m) (hPQ : P ∣ Q)
    (h3 : ¬ 3 ∣ x → 3 * P ∣ Q) : 3 * (x ^ m * P) ∣ (x ^ 3) ^ m * Q := by
  by_cases hx : 3 ∣ x
  · have e : (x ^ 3) ^ m = x ^ m * x ^ (2 * m) := by
      rw [← pow_mul, ← pow_add]
      ring_nf
    have h3x : 3 ∣ x ^ (2 * m) := dvd_pow hx (by omega)
    rw [e]
    calc 3 * (x ^ m * P) = x ^ m * (3 * P) := by ring
      _ ∣ x ^ m * (x ^ (2 * m) * Q) := mul_dvd_mul_left _ (mul_dvd_mul h3x hPQ)
      _ = x ^ m * x ^ (2 * m) * Q := by ring
  · have hxm : x ^ m ∣ (x ^ 3) ^ m := pow_dvd_pow_of_dvd (dvd_pow_self x (by norm_num)) m
    calc 3 * (x ^ m * P) = x ^ m * (3 * P) := by ring
      _ ∣ (x ^ 3) ^ m * Q := mul_dvd_mul hxm (h3 hx)

theorem one_le_choose_two {n : ℕ} (hn : 2 ≤ n) : 1 ≤ n * (n - 1) / 2 := by
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  rw [show k + 2 - 1 = k + 1 by omega]
  nlinarith

theorem three_mul_lieOrderNumerator_psl_dvd {n : ℕ} (hn : 2 ≤ n) (x : ℕ) :
    3 * lieOrderNumerator .PSL n x ∣ lieOrderNumerator .PSL n (x ^ 3) := by
  rw [lieOrderNumerator_psl, lieOrderNumerator_psl]
  refine three_mul_pow_mul_dvd (one_le_choose_two hn) ?_ fun hx => ?_
  · refine Finset.prod_dvd_prod_of_dvd _ _ fun i _ => ?_
    simpa [← pow_mul, mul_comm] using Nat.sub_dvd_pow_sub_pow (x ^ i) 1 3
  · refine three_mul_prod_dvd_of_two hn (fun i _ => ?_) (three_mul_sub_one_dvd_cube hx)
    simpa [← pow_mul, mul_comm] using Nat.sub_dvd_pow_sub_pow (x ^ i) 1 3

theorem three_mul_lieOrderNumerator_psu_dvd {n : ℕ} (hn : 2 ≤ n) (x : ℕ) :
    3 * lieOrderNumerator .PSU n x ∣ lieOrderNumerator .PSU n (x ^ 3) := by
  have hab : ∀ i : ℕ, (if Even i then x ^ i - 1 else x ^ i + 1) ∣
      (if Even i then (x ^ 3) ^ i - 1 else (x ^ 3) ^ i + 1) := by
    intro i
    by_cases hi : Even i
    · simp only [hi, if_true]
      simpa [← pow_mul, mul_comm] using Nat.sub_dvd_pow_sub_pow (x ^ i) 1 3
    · simp only [hi, if_false]
      simpa [← pow_mul, mul_comm] using
        Odd.nat_add_dvd_pow_add_pow (x ^ i) 1 (n := 3) (by decide)
  rw [lieOrderNumerator_psu, lieOrderNumerator_psu]
  refine three_mul_pow_mul_dvd (one_le_choose_two hn) ?_ fun hx => ?_
  · exact Finset.prod_dvd_prod_of_dvd _ _ fun i _ => hab i
  · refine three_mul_prod_dvd_of_two hn (fun i _ => hab i) ?_
    simpa using three_mul_sub_one_dvd_cube hx

theorem lieOrderNumerator_psl_pos {n x : ℕ} (hx : 2 ≤ x) : 0 < lieOrderNumerator .PSL n x := by
  rw [lieOrderNumerator_psl]
  refine Nat.mul_pos (pow_pos (by omega) _) (Finset.prod_pos fun i hi => ?_)
  have hi2 : 2 ≤ i := (Finset.mem_Icc.1 hi).1
  exact Nat.sub_pos_of_lt (Nat.one_lt_pow (by omega) (by omega))

theorem lieOrderNumerator_psu_pos {n x : ℕ} (hx : 2 ≤ x) : 0 < lieOrderNumerator .PSU n x := by
  rw [lieOrderNumerator_psu]
  refine Nat.mul_pos (pow_pos (by omega) _) (Finset.prod_pos fun i hi => ?_)
  have hi2 : 2 ≤ i := (Finset.mem_Icc.1 hi).1
  split_ifs
  · exact Nat.sub_pos_of_lt (Nat.one_lt_pow (by omega) (by omega))
  · omega

theorem exists_mul_three_dvd {C N S D : ℕ} (hN : 0 < N) (hCN : C ∣ N) (hCS : C ∣ S)
    (h : 3 * N ∣ S * D) (hD : ¬ 3 ∣ D) : ∃ M, C ∣ M ∧ 3 * M ∣ S := by
  refine ⟨Nat.gcd N S, Nat.dvd_gcd hCN hCS, ?_⟩
  have hg : 0 < Nat.gcd N S := Nat.gcd_pos_of_pos_left _ hN
  obtain ⟨n₀, s, hcop, hn₀, hs⟩ := Nat.exists_coprime N S
  generalize Nat.gcd N S = g at hg hn₀ hs ⊢
  subst hn₀ hs
  have hn₀pos : 0 < n₀ := Nat.pos_of_ne_zero fun h => by simp [h] at hN
  have h1 : 3 * n₀ ∣ s * D := by
    have : 3 * n₀ * g ∣ s * D * g := by
      convert h using 1 <;> ring
    exact Nat.dvd_of_mul_dvd_mul_right hg this
  have h2 : n₀ ∣ D := hcop.dvd_of_dvd_mul_left ((Dvd.intro_left 3 rfl).trans h1)
  obtain ⟨d, rfl⟩ := h2
  have h3 : 3 ∣ s * d := by
    have : n₀ * 3 ∣ n₀ * (s * d) := by
      convert h1 using 1 <;> ring
    exact Nat.dvd_of_mul_dvd_mul_left hn₀pos this
  rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3 with h4 | h4
  · exact mul_dvd_mul_right h4 g
  · exact absurd (h4.mul_left n₀) hD

end CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route
