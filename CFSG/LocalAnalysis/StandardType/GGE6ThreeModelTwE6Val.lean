module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotSwapConjGenArith

public section

namespace CFSG.StandardType.E6ThreeModel

open CFSG.SeitzReduction.E6Pilot

private theorem padicValNat_list_prod {p : ℕ} [Fact p.Prime] (l : List ℕ)
    (h : ∀ x ∈ l, x ≠ 0) :
    padicValNat p l.prod = (l.map (padicValNat p)).sum := by
  induction l with
  | nil => simp [padicValNat.one]
  | cons x xs ih =>
      have hxs : xs.prod ≠ 0 := by
        apply List.prod_ne_zero
        intro h0
        exact h 0 (by simp [h0]) rfl
      rw [List.prod_cons, List.map_cons, List.sum_cons,
        padicValNat.mul (h x (by simp)) hxs]
      rw [ih (fun y hy => h y (by simp [hy]))]

theorem not_dvd_numTwistedE6 {q : ℕ} (hq : 2 ≤ q) (h3 : 3 ∣ q + 1) :
    ¬ ((q + 1) ^ 6 * 3 ^ 5 ∣ numTwistedE6 q) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq1 : 1 < q := by omega
  have h3q : ¬ 3 ∣ q := by
    intro h
    have h' : 3 ∣ (q + 1) - q := Nat.dvd_sub h3 h
    have h1 : (q + 1) - q = 1 := by omega
    rw [h1] at h'
    have := Nat.dvd_one.mp h'
    omega
  have h3qsub : ¬ 3 ∣ q - 1 := by
    intro h
    have h' : 3 ∣ (q + 1) - (q - 1) := Nat.dvd_sub h3 h
    have h1 : (q + 1) - (q - 1) = 2 := by omega
    rw [h1] at h'
    have := Nat.le_of_dvd (by norm_num : 0 < 2) h'
    omega
  have h2eq : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    have h := Nat.sq_sub_sq q 1
    rw [one_pow] at h
    rw [h, mul_comm]
  have h3q2sub : 3 ∣ q ^ 2 - 1 := by
    rw [h2eq]
    exact dvd_mul_of_dvd_right h3 (q - 1)
  have h3q2 : ¬ 3 ∣ q ^ 2 := fun h => h3q (Nat.prime_three.dvd_of_dvd_pow h)
  have h1ltq2 : 1 < q ^ 2 := Nat.one_lt_pow (by norm_num) hq1
  have v36 : padicValNat 3 (q ^ 36) = 0 :=
    padicValNat.eq_zero_of_not_dvd (fun h => h3q (Nat.prime_three.dvd_of_dvd_pow h))
  have v2 : padicValNat 3 (q ^ 2 - 1) = padicValNat 3 (q + 1) := by
    rw [h2eq, padicValNat.mul (by omega : q - 1 ≠ 0) (by omega : q + 1 ≠ 0),
      padicValNat.eq_zero_of_not_dvd h3qsub, zero_add]
  have v5 : padicValNat 3 (q ^ 5 + 1) = padicValNat 3 (q + 1) := by
    have h := padicValNat.pow_add_pow (p := 3) (x := q) (y := 1) (by decide : Odd 3) h3 h3q
      (by decide : Odd 5)
    rw [one_pow, padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 5), add_zero] at h
    exact h
  have v9 : padicValNat 3 (q ^ 9 + 1) = padicValNat 3 (q + 1) + 2 := by
    have h := padicValNat.pow_add_pow (p := 3) (x := q) (y := 1) (by decide : Odd 3) h3 h3q
      (by decide : Odd 9)
    rw [one_pow] at h
    have h9 : padicValNat 3 9 = 2 := by
      have : (9 : ℕ) = 3 ^ 2 := by norm_num
      rw [this, padicValNat_base_pow (by norm_num)]
    rw [h9] at h
    exact h
  have v6 : padicValNat 3 (q ^ 6 - 1) = padicValNat 3 (q + 1) + 1 := by
    have h := padicValNat.pow_sub_pow (p := 3) (x := q ^ 2) (y := 1) (by decide : Odd 3)
      h1ltq2 h3q2sub h3q2 (by norm_num : (3 : ℕ) ≠ 0)
    rw [one_pow] at h
    have hpow : (q ^ 2) ^ 3 = q ^ 6 := by rw [← pow_mul]
    rw [hpow, padicValNat.self (by norm_num), v2] at h
    exact h
  have v8 : padicValNat 3 (q ^ 8 - 1) = padicValNat 3 (q + 1) := by
    have h := padicValNat.pow_sub_pow (p := 3) (x := q ^ 2) (y := 1) (by decide : Odd 3)
      h1ltq2 h3q2sub h3q2 (by norm_num : (4 : ℕ) ≠ 0)
    rw [one_pow] at h
    have hpow : (q ^ 2) ^ 4 = q ^ 8 := by rw [← pow_mul]
    rw [hpow, padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 4), add_zero, v2] at h
    exact h
  have v12 : padicValNat 3 (q ^ 12 - 1) = padicValNat 3 (q + 1) + 1 := by
    have h := padicValNat.pow_sub_pow (p := 3) (x := q ^ 2) (y := 1) (by decide : Odd 3)
      h1ltq2 h3q2sub h3q2 (by norm_num : (6 : ℕ) ≠ 0)
    rw [one_pow] at h
    have hpow : (q ^ 2) ^ 6 = q ^ 12 := by rw [← pow_mul]
    have h6 : padicValNat 3 6 = 1 := by
      have hm : (6 : ℕ) = 3 * 2 := by norm_num
      rw [hm, padicValNat.mul (by norm_num) (by norm_num), padicValNat.self (by norm_num),
        padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 2), add_zero]
    rw [hpow, h6, v2] at h
    exact h
  have hlist : numTwistedE6 q =
      [q ^ 36, q ^ 12 - 1, q ^ 9 + 1, q ^ 8 - 1, q ^ 6 - 1, q ^ 5 + 1, q ^ 2 - 1].prod := by
    simp only [List.prod_cons, List.prod_nil, mul_one]
    unfold numTwistedE6
    ac_rfl
  have hl : ∀ x ∈ [q ^ 36, q ^ 12 - 1, q ^ 9 + 1, q ^ 8 - 1, q ^ 6 - 1, q ^ 5 + 1, q ^ 2 - 1],
      x ≠ 0 := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact pow_ne_zero _ (by omega)
    · have : 1 < q ^ 12 := Nat.one_lt_pow (by norm_num) hq1
      omega
    · omega
    · have : 1 < q ^ 8 := Nat.one_lt_pow (by norm_num) hq1
      omega
    · have : 1 < q ^ 6 := Nat.one_lt_pow (by norm_num) hq1
      omega
    · omega
    · have : 1 < q ^ 2 := Nat.one_lt_pow (by norm_num) hq1
      omega
  have hval : padicValNat 3 (numTwistedE6 q) = 6 * padicValNat 3 (q + 1) + 4 := by
    rw [hlist, padicValNat_list_prod _ hl]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [v36, v12, v9, v8, v6, v5, v2]
    ring
  have hN : numTwistedE6 q ≠ 0 := by
    rw [hlist]
    exact List.prod_ne_zero (by intro h0; exact hl 0 h0 rfl)
  intro hdvd
  have h3a : 3 ^ padicValNat 3 (q + 1) ∣ q + 1 := pow_padicValNat_dvd
  have h3a6 : 3 ^ (6 * padicValNat 3 (q + 1)) ∣ (q + 1) ^ 6 := by
    have h := pow_dvd_pow_of_dvd h3a 6
    have heq : (3 ^ padicValNat 3 (q + 1)) ^ 6 = 3 ^ (6 * padicValNat 3 (q + 1)) := by
      rw [← pow_mul]
      congr 1
      ring
    rwa [heq] at h
  have hdvd3 : 3 ^ (6 * padicValNat 3 (q + 1) + 5) ∣ numTwistedE6 q := by
    have hmul : 3 ^ (6 * padicValNat 3 (q + 1)) * 3 ^ 5 ∣ (q + 1) ^ 6 * 3 ^ 5 :=
      mul_dvd_mul h3a6 dvd_rfl
    rw [← pow_add] at hmul
    exact hmul.trans hdvd
  have hle := (padicValNat_dvd_iff_le hN).mp hdvd3
  rw [hval] at hle
  omega

end CFSG.StandardType.E6ThreeModel
