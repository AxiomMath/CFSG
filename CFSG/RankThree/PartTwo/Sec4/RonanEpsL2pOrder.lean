module

public import CFSG.RankThree.PartTwo.Sec4.RonanEpsLieTools

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanEps

theorem psl2_core_m {x L m ε : ℤ} (hx : 8 ≤ x) (hL : 5 ≤ L) (hm : 1 ≤ m) (hε : ε ^ 2 = 1)
    (h1 : L * m = x ^ 3 + ε) (h2 : L ^ 2 - 1 = 2 * x ^ 3 * (x ^ 2 - 1) * m) : False := by
  have hε' : ε = 1 ∨ ε = -1 := by
    have h : (ε - 1) * (ε + 1) = 0 := by linear_combination hε
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  have hε1 : -1 ≤ ε ∧ ε ≤ 1 := by
    rcases hε' with rfl | rfl <;> norm_num
  have hx0 : (0 : ℤ) < x := by linarith
  have hx3 : 0 < x ^ 3 := pow_pos hx0 3
  have hLm : L ≤ L * m := by
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ L - 5 by linarith) (show (0 : ℤ) ≤ m - 1 by linarith)]
  have hLx : L ≤ x ^ 3 + 1 := by linarith [hε1.2]
  have hL2 : L ^ 2 ≤ (x ^ 3 + 1) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hLx) (show (0 : ℤ) ≤ x ^ 3 + 1 + L by linarith)]
  have hb : x ^ 3 * (2 * (x ^ 2 - 1) * m) ≤ x ^ 3 * (x ^ 3 + 2) := by nlinarith
  have hb' : 2 * (x ^ 2 - 1) * m ≤ x ^ 3 + 2 := le_of_mul_le_mul_left hb hx3
  have hmx : m ≤ x := by
    by_contra hc
    have hc' : x + 1 ≤ m := by omega
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ x ^ 2 - 1 by nlinarith)
        (show (0 : ℤ) ≤ m - (x + 1) by linarith),
      mul_nonneg (show (0 : ℤ) ≤ x - 8 by linarith) (show (0 : ℤ) ≤ x ^ 2 by positivity),
      mul_nonneg (show (0 : ℤ) ≤ x - 8 by linarith) hx0.le]
  have hmm : m * m ≤ x * x := mul_le_mul hmx hmx (by linarith) hx0.le
  have hm2 : m ^ 2 ≤ x ^ 3 := by
    nlinarith [mul_nonneg (mul_nonneg hx0.le hx0.le) (show (0 : ℤ) ≤ x - 1 by linarith)]
  obtain ⟨K, hK⟩ : ∃ K : ℤ, K = x ^ 3 + 2 * ε - 2 * (x ^ 2 - 1) * m ^ 3 := ⟨_, rfl⟩
  have hid : m ^ 2 - 1 = x ^ 3 * K := by
    rw [hK]
    linear_combination (-m ^ 2) * h2 + (L * m + x ^ 3 + ε) * h1 + hε
  have hm1sq : 1 ≤ m ^ 2 := by nlinarith
  have hK0 : 0 ≤ K := by
    by_contra hc
    have hc' : K ≤ -1 := by omega
    have h3 : x ^ 3 * K ≤ x ^ 3 * (-1) := mul_le_mul_of_nonneg_left hc' hx3.le
    linarith
  have hK1 : K < 1 := by
    by_contra hc
    have hc' : 1 ≤ K := by omega
    have h3 : x ^ 3 * 1 ≤ x ^ 3 * K := mul_le_mul_of_nonneg_left hc' hx3.le
    linarith
  have hK2 : K = 0 := by omega
  rw [hK2, mul_zero] at hid
  have hmfac : (m - 1) * (m + 1) = 0 := by linear_combination hid
  have hm_eq : m = 1 := by
    rcases mul_eq_zero.mp hmfac with h | h
    · linarith
    · linarith
  subst hm_eq
  rcases hε' with rfl | rfl
  ·
    have hL' : L = x ^ 3 + 1 := by linarith
    subst hL'
    have key : x ^ 3 * (x ^ 3 - 2 * x ^ 2 + 4) = 0 := by linear_combination h2
    rcases mul_eq_zero.mp key with h | h
    · linarith
    · nlinarith [mul_nonneg (sq_nonneg x) (show (0 : ℤ) ≤ x - 2 by linarith)]
  ·
    have hL' : L = x ^ 3 - 1 := by linarith
    subst hL'
    have key : x ^ 5 * (x - 2) = 0 := by linear_combination h2
    rcases mul_eq_zero.mp key with h | h
    · have : 0 < x ^ 5 := pow_pos hx0 5
      linarith
    · linarith

theorem psl2_core_six {x L M N : ℤ} (hx : 8 ≤ x) (hL : 5 ≤ L) (hLx : L ≤ x ^ 2 - 1)
    (hM : x ^ 3 - 1 ≤ M) (hX : 2 * N = L * (L ^ 2 - 1)) (hN : N = x ^ 3 * ((x ^ 2 - 1) * M)) :
    False := by
  have hx0 : (0 : ℤ) < x := by linarith
  have hx3 : 0 < x ^ 3 := pow_pos hx0 3
  have hx4 : 0 < x ^ 4 := pow_pos hx0 4
  have hx3ge : (512 : ℤ) ≤ x ^ 3 := by
    nlinarith [pow_nonneg (show (0 : ℤ) ≤ x - 8 by linarith) 3, sq_nonneg (x - 8)]
  have hLlt : L < x ^ 2 := by linarith
  have hL2 : L ^ 2 < x ^ 4 := by
    nlinarith [mul_pos (sub_pos.mpr hLlt) (show (0 : ℤ) < x ^ 2 + L by linarith)]
  have hL3 : L ^ 3 < x ^ 6 := by
    nlinarith [mul_pos (sub_pos.mpr hLlt) hx4,
      mul_pos (show (0 : ℤ) < L by linarith) (sub_pos.mpr hL2)]
  have h1 : L * (L ^ 2 - 1) < x ^ 6 := by nlinarith
  have hA : x ^ 3 - 1 ≤ (x ^ 2 - 1) * M := by
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ x ^ 2 - 2 by nlinarith) (show (0 : ℤ) ≤ M by linarith)]
  have h2 : x ^ 6 ≤ 2 * N := by
    rw [hN]
    nlinarith [mul_le_mul_of_nonneg_left hA hx3.le,
      mul_nonneg hx3.le (show (0 : ℤ) ≤ x ^ 3 - 2 by linarith)]
  linarith

theorem psl2_false_of_card {N r M ℓ : ℕ} {ε : ℤ} (hℓ : ℓ.Prime) (h5 : 5 ≤ ℓ)
    (hX : 2 * N = ℓ * (ℓ ^ 2 - 1)) (hr2 : 2 ≤ r) (hℓr : ¬ ℓ ∣ r)
    (hN : N = r ^ 9 * ((r ^ 6 - 1) * M)) (hε : ε ^ 2 = 1)
    (hMε : (M : ℤ) = (r : ℤ) ^ 9 + ε) : False := by
  have hℓpos : 0 < ℓ := hℓ.pos
  have hr6 : 1 ≤ r ^ 6 := Nat.one_le_pow _ _ (by omega)
  have hdvd : ℓ ∣ 2 * (r ^ 9 * ((r ^ 6 - 1) * M)) := by
    rw [← hN, hX]
    exact dvd_mul_right ℓ _
  rcases (Nat.Prime.dvd_mul hℓ).mp hdvd with h2 | h9
  · have := Nat.le_of_dvd (by norm_num) h2
    omega
  rcases (Nat.Prime.dvd_mul hℓ).mp h9 with hr9 | h6M
  · exact hℓr (hℓ.dvd_of_dvd_pow hr9)
  have h8 : 8 ≤ r ^ 3 := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ r ^ 3 := Nat.pow_le_pow_left hr2 3
  have h8Z : (8 : ℤ) ≤ (r : ℤ) ^ 3 := by exact_mod_cast h8
  have hεZ : -1 ≤ ε := by nlinarith [sq_nonneg (ε + 1)]
  have hL5 : (5 : ℤ) ≤ ℓ := by exact_mod_cast h5
  have hℓZ : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  have h1ℓ : 1 ≤ ℓ ^ 2 := Nat.one_le_pow _ _ hℓpos
  have hX' : (2 : ℤ) * (N : ℤ) = (ℓ : ℤ) * ((ℓ : ℤ) ^ 2 - 1) := by
    have h := hX
    zify [h1ℓ] at h
    linarith
  have hN' : (N : ℤ) = ((r : ℤ) ^ 3) ^ 3 * ((((r : ℤ) ^ 3) ^ 2 - 1) * (M : ℤ)) := by
    have h := hN
    zify [hr6] at h
    rw [h]
    ring
  rcases (Nat.Prime.dvd_mul hℓ).mp h6M with h6 | hM
  ·
    have h64 : 64 ≤ r ^ 6 := by
      calc 64 = 2 ^ 6 := by norm_num
        _ ≤ r ^ 6 := Nat.pow_le_pow_left hr2 6
    have h6pos : 0 < r ^ 6 - 1 := by omega
    have hLle : ℓ ≤ r ^ 6 - 1 := Nat.le_of_dvd h6pos h6
    have hLleZ : (ℓ : ℤ) ≤ ((r : ℤ) ^ 3) ^ 2 - 1 := by
      have h := hLle
      zify [hr6] at h
      linarith [show ((r : ℤ) ^ 3) ^ 2 = (r : ℤ) ^ 6 by ring]
    have hx9 : ((r : ℤ) ^ 3) ^ 3 = (r : ℤ) ^ 9 := by ring
    have hMZ : ((r : ℤ) ^ 3) ^ 3 - 1 ≤ (M : ℤ) := by
      rw [hx9, hMε]
      linarith
    exact psl2_core_six h8Z hL5 hLleZ hMZ hX' hN'
  ·
    obtain ⟨m, hmM⟩ := hM
    have hMm : (M : ℤ) = (ℓ : ℤ) * (m : ℤ) := by exact_mod_cast hmM
    have h512 : (512 : ℤ) ≤ ((r : ℤ) ^ 3) ^ 3 := by
      nlinarith [pow_nonneg (show (0 : ℤ) ≤ (r : ℤ) ^ 3 - 8 by linarith) 3,
        sq_nonneg ((r : ℤ) ^ 3 - 8)]
    have hMpos : (1 : ℤ) ≤ M := by
      rw [hMε]
      linarith
    have hm1 : (1 : ℤ) ≤ m := by
      by_contra hc
      have hm0 : (m : ℤ) ≤ 0 := by omega
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ ℓ by linarith) (show (0 : ℤ) ≤ -(m : ℤ) by linarith)]
    have h1 : (ℓ : ℤ) * m = ((r : ℤ) ^ 3) ^ 3 + ε := by
      linear_combination hMε - hMm
    have key : (ℓ : ℤ) * ((ℓ : ℤ) ^ 2 - 1) =
        (ℓ : ℤ) * (2 * ((r : ℤ) ^ 3) ^ 3 * (((r : ℤ) ^ 3) ^ 2 - 1) * (m : ℤ)) := by
      linear_combination (-1 : ℤ) * hX' + 2 * hN' + 2 * (r : ℤ) ^ 9 * ((r : ℤ) ^ 6 - 1) * hMm
    have h2' := mul_left_cancel₀ hℓZ key
    exact psl2_core_m h8Z hL5 hm1 hε h1 h2'

theorem not_isTypeEpsCube_of_two_mul_card_eq_psl2_prime {X : Type} [Group X] {ℓ : ℕ}
    (hℓ : ℓ.Prime) (h5 : 5 ≤ ℓ) (hX : 2 * Nat.card X = ℓ * (ℓ ^ 2 - 1)) : ¬ IsTypeEpsCube X := by
  intro h
  obtain ⟨p, g, hp, -, hg, hcase⟩ := card_of_isTypeEpsCube_prime h
  have hpg : 2 ≤ p ^ g := hp.two_le.trans (Nat.le_self_pow (by omega) p)
  have h1ℓ : 1 ≤ ℓ ^ 2 := Nat.one_le_pow _ _ hℓ.pos
  have hpℓ : p ≠ ℓ := by
    intro hpl
    have hℓr : ℓ ∣ p ^ g := by
      rw [← hpl]
      exact dvd_pow_self p (by omega)
    have hr9 : ℓ ^ 2 ∣ (p ^ g) ^ 9 :=
      (pow_dvd_pow ℓ (by norm_num : 2 ≤ 9)).trans (pow_dvd_pow_of_dvd hℓr 9)
    have h2 : ℓ ^ 2 ∣ Nat.card X := by
      rcases hcase with ⟨-, hN⟩ | ⟨-, hN⟩ <;> rw [hN] <;> exact hr9.trans (dvd_mul_right _ _)
    have h3 : ℓ ^ 2 ∣ ℓ * (ℓ ^ 2 - 1) := by
      rw [← hX]
      exact h2.mul_left 2
    have h4 : ℓ ∣ ℓ ^ 2 - 1 := by
      have h3' : ℓ * ℓ ∣ ℓ * (ℓ ^ 2 - 1) := by
        rw [← pow_two]
        exact h3
      exact Nat.dvd_of_mul_dvd_mul_left hℓ.pos h3'
    have h5' : ℓ ∣ 1 := by
      have h6 : ℓ ∣ ℓ ^ 2 := dvd_pow_self ℓ two_ne_zero
      have h7 := Nat.dvd_sub h6 h4
      rwa [show ℓ ^ 2 - (ℓ ^ 2 - 1) = 1 by omega] at h7
    have := Nat.le_of_dvd one_pos h5'
    omega
  have hℓr : ¬ ℓ ∣ p ^ g := fun hd =>
    hpℓ ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp (hℓ.dvd_of_dvd_pow hd)).symm
  rcases hcase with ⟨-, hN⟩ | ⟨-, hN⟩
  · refine psl2_false_of_card (N := Nat.card X) (r := p ^ g) (M := (p ^ g) ^ 9 - 1) (ε := -1)
      hℓ h5 hX hpg hℓr hN (by norm_num) ?_
    rw [Nat.cast_sub (Nat.one_le_pow 9 (p ^ g) (pow_pos hp.pos g))]
    push_cast <;> ring
  · refine psl2_false_of_card (N := Nat.card X) (r := p ^ g) (M := (p ^ g) ^ 9 + 1) (ε := 1)
      hℓ h5 hX hpg hℓr hN (by norm_num) ?_
    push_cast <;> ring

end CFSG.RankThree.PartTwo.Sec4.RonanEps
