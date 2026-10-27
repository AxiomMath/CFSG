module

public import CFSG.Walter.ReeOrder.Ward.ArithEight

public section

namespace CFSG.Walter.Ward

theorem isCoprime_of_sub {x y e : ℤ} (he : IsSign e) (h : y = x + e) : IsCoprime x y :=
  ⟨-e, e, by rw [h]; linear_combination he.sq⟩

theorem seven_ineq₁ {q e : ℤ} (he : IsSign e) (hq : 27 ≤ q) :
    (q ^ 2 - 1) * (q + e) < q * (2 * (q * (q + e)) - 2 * q - e) := by
  rcases he with rfl | rfl <;> nlinarith [mul_pos (by omega : (0 : ℤ) < q) (by omega : (0 : ℤ) < q)]

theorem seven_ineq₂ {q e : ℤ} (he : IsSign e) (hq : 27 ≤ q) :
    (q ^ 2 - 1) * (q + e) < q * (2 * (q * (q + e) - 2 * q - e)) := by
  rcases he with rfl | rfl <;> nlinarith [mul_pos (by omega : (0 : ℤ) < q) (by omega : (0 : ℤ) < q)]

theorem seven_ineq₃ {q e : ℤ} (he : IsSign e) (hq : 27 ≤ q) :
    (q ^ 2 - 1) * (q + e) * (q - e) < q * (q ^ 3 + e) := by
  rcases he with rfl | rfl <;> nlinarith [mul_pos (by omega : (0 : ℤ) < q) (by omega : (0 : ℤ) < q)]

theorem seven_numth {p m : ℕ} (hp : p.Prime) {q e a d R : ℤ} (hqpm : q = (p : ℤ) ^ m)
    (hq : 27 ≤ q) (he : IsSign e) (hq8 : q % 8 = 4 + e) (ha : 0 < a) (pd : 0 < d)
    (hdev : Even d) (h4 : q * a * (d + q - e) ^ 2 = (q ^ 2 - 1) * (q + e) * d * (d - e))
    (hint : d ∣ q ^ 2 * a * (q - e)) (hR : 2 * R = q + e) (hRo : R ∣ d - 2 * e) :
    e = 1 ∧ d = q * (q - 1) ∧ a = q ^ 2 - q - 1 := by
  have hee := he.sq
  have hq0 : 0 < q := by omega
  have hqe : 0 < q + e := by rcases he with rfl | rfl <;> omega
  have hqme : 0 < q - e := by rcases he with rfl | rfl <;> omega
  have hd2 : 2 ≤ d := by
    obtain ⟨k, hk⟩ := hdev
    omega
  have pde : 0 < d - e := by rcases he with rfl | rfl <;> omega
  have hlt : q * a < (q ^ 2 - 1) * (q + e) := by
    have h1 : d * (d - e) < (d + q - e) ^ 2 := by
      have h2 : d < d + q - e := by linarith
      have h3 : d - e < d + q - e := by linarith
      rw [sq]
      exact mul_lt_mul'' h2 h3 pd.le pde.le
    have h5 : 0 < (q ^ 2 - 1) * (q + e) := by
      have : 0 < q ^ 2 - 1 := by nlinarith
      positivity
    by_contra hc
    push Not at hc
    have : (q ^ 2 - 1) * (q + e) * (d * (d - e)) < q * a * (d + q - e) ^ 2 := by
      calc (q ^ 2 - 1) * (q + e) * (d * (d - e)) < (q ^ 2 - 1) * (q + e) * (d + q - e) ^ 2 :=
            mul_lt_mul_of_pos_left h1 h5
        _ ≤ q * a * (d + q - e) ^ 2 := mul_le_mul_of_nonneg_right hc (sq_nonneg _)
    linarith
  have hcopq1 : IsCoprime q ((q ^ 2 - 1) * (q + e)) := by
    apply IsCoprime.mul_right
    · exact ⟨q, -1, by ring⟩
    · exact isCoprime_of_sub he rfl
  have hqdd : q ∣ d * (d - e) := by
    have : q ∣ (q ^ 2 - 1) * (q + e) * (d * (d - e)) :=
      ⟨a * (d + q - e) ^ 2, by linear_combination -h4⟩
    exact hcopq1.dvd_of_dvd_mul_left this
  have hcopd : IsCoprime (d - e) d := isCoprime_of_sub he (by ring)
  have hsplit := prime_pow_dvd_mul_of_coprime (m := m) hp hcopd.symm (by rw [← hqpm]; exact hqdd)
  rw [← hqpm] at hsplit
  rcases hsplit with hqd | hqd
  ·
    have hcopq : IsCoprime q (d - e) := by
      obtain ⟨k, hk⟩ := hqd
      rw [hk]
      exact ⟨e * k, -e, by linear_combination hee⟩
    have hda : d - e ∣ a := by
      have h1 : d - e ∣ q * a * (d + q - e) ^ 2 := ⟨(q ^ 2 - 1) * (q + e) * d, by rw [h4]; ring⟩
      have h2 : IsCoprime (d - e) (q * (d + q - e) ^ 2) := by
        apply IsCoprime.mul_right hcopq.symm
        apply IsCoprime.pow_right
        have : d + q - e = q + (d - e) * 1 := by ring
        rw [this]
        exact IsCoprime.add_mul_left_right hcopq.symm 1
      have h3 : d - e ∣ q * (d + q - e) ^ 2 * a := by
        have e1 : q * (d + q - e) ^ 2 * a = q * a * (d + q - e) ^ 2 := by ring
        rw [e1]
        exact h1
      exact h2.dvd_of_dvd_mul_left h3
    have hdea : d - e ≤ a := Int.le_of_dvd ha hda
    have hqdea : q * (d - e) ≤ q * a := mul_le_mul_of_nonneg_left hdea hq0.le
    have hRodd : Odd R := by
      rcases he with rfl | rfl
      · exact ⟨(R - 1) / 2, by omega⟩
      · exact ⟨(R - 1) / 2, by omega⟩
    obtain ⟨t, ht⟩ := hRo
    have htev : Even t := by
      have hev : Even (d - 2 * e) := by
        obtain ⟨k, hk⟩ := hdev
        exact ⟨k - e, by omega⟩
      rw [ht] at hev
      rcases Int.even_or_odd t with h | h
      · exact h
      · exact absurd hev (Int.not_even_iff_odd.mpr (Int.odd_mul.mpr ⟨hRodd, h⟩))
    obtain ⟨k, hk⟩ := htev
    have hdk : d - 2 * e = (q + e) * k := by rw [ht, hk]; linear_combination k * hR
    have hqk : q ∣ k + 2 := by
      have h1 : q ∣ e * (k + 2) := by
        have : e * (k + 2) = d - q * k := by linear_combination -hdk
        rw [this]
        exact dvd_sub hqd (dvd_mul_right q k)
      have hcqe : IsCoprime q e := ⟨0, e, by linear_combination hee⟩
      exact hcqe.dvd_of_dvd_mul_left h1
    obtain ⟨j, hj⟩ := hqk
    have hdj : d = j * (q * (q + e)) - 2 * q := by
      have : k = q * j - 2 := by linarith
      rw [this] at hdk
      linear_combination hdk
    have hqq : 0 < q * (q + e) := by positivity
    have hj1 : 1 ≤ j := by
      by_contra h
      push Not at h
      have : j * (q * (q + e)) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by omega) hqq.le
      linarith
    have hj : j = 1 := by
      by_contra h
      have hj2 : 2 ≤ j := by omega
      have h1 : 2 * (q * (q + e)) - 2 * q - e ≤ d - e := by
        rw [hdj]
        have := mul_le_mul_of_nonneg_right hj2 hqq.le
        linarith
      have h2 := mul_le_mul_of_nonneg_left h1 hq0.le
      have h3 := seven_ineq₁ he hq
      linarith
    rw [hj, one_mul] at hdj
    obtain ⟨c, hc⟩ := hda
    have hc1 : c = 1 := by
      have hc0 : 0 < c := by
        by_contra h
        push Not at h
        have : (d - e) * c ≤ 0 := mul_nonpos_of_nonneg_of_nonpos pde.le h
        linarith
      by_contra h
      have hc2 : 2 ≤ c := by omega
      have h1 : 2 * (d - e) ≤ a := by
        rw [hc]
        have := mul_le_mul_of_nonneg_left hc2 pde.le
        linarith
      have h2 := mul_le_mul_of_nonneg_left h1 hq0.le
      rw [hdj] at h2
      have h3 := seven_ineq₂ he hq
      linarith
    rw [hc1, mul_one] at hc
    rw [hc, hdj] at h4
    rcases he with rfl | rfl
    · refine ⟨rfl, by rw [hdj]; ring, by rw [hc, hdj]; ring⟩
    · exfalso
      have hq1 : (q - 1) ^ 2 * q * (q * (q + -1) - 2 * q - -1) ≠ 0 := by
        have : 0 < q * (q + -1) - 2 * q - -1 := by nlinarith
        have : 0 < (q - 1) ^ 2 * q := by positivity
        positivity
      have : (q - 1) ^ 2 * q * (q * (q + -1) - 2 * q - -1) * ((q - 1) ^ 2) =
          (q - 1) ^ 2 * q * (q * (q + -1) - 2 * q - -1) * ((q + 1) * (q - 3)) := by
        linear_combination h4
      have := mul_left_cancel₀ hq1 this
      nlinarith
  ·
    exfalso
    have hcopq : IsCoprime q d := by
      obtain ⟨k, hk⟩ := hqd
      have : d = q * k + e := by linarith
      rw [this]
      exact ⟨-e * k, e, by linear_combination hee⟩
    have hq2 : q ^ 2 ∣ (d + q - e) ^ 2 := by
      obtain ⟨k, hk⟩ := hqd
      exact ⟨(k + 1) ^ 2, by rw [show d + q - e = (d - e) + q by ring, hk]; ring⟩
    have hq3 : q ^ 3 ∣ (q ^ 2 - 1) * (q + e) * d * (d - e) := by
      rw [← h4]
      obtain ⟨u, hu⟩ := hq2
      exact ⟨a * u, by rw [hu]; ring⟩
    have hcop3 : IsCoprime (q ^ 3) ((q ^ 2 - 1) * (q + e) * d) := by
      apply IsCoprime.pow_left
      exact IsCoprime.mul_right hcopq1 hcopq
    have hq3d : q ^ 3 ∣ d - e := hcop3.dvd_of_dvd_mul_left hq3
    have hbig : q ^ 3 ≤ d - e := Int.le_of_dvd pde hq3d
    have hda : d ∣ a * (q - e) := by
      have hc : IsCoprime d (q ^ 2) := hcopq.symm.pow_right
      have e1 : q ^ 2 * (a * (q - e)) = q ^ 2 * a * (q - e) := by ring
      apply hc.dvd_of_dvd_mul_left
      rw [e1]
      exact hint
    have hdle : d ≤ a * (q - e) := Int.le_of_dvd (by positivity) hda
    have h1 : q * (q ^ 3 + e) ≤ q * (a * (q - e)) :=
      mul_le_mul_of_nonneg_left (by linarith) hq0.le
    have h2 : q * a * (q - e) < (q ^ 2 - 1) * (q + e) * (q - e) :=
      mul_lt_mul_of_pos_right hlt hqme
    have h3 := seven_ineq₃ he hq
    linarith

theorem seven_quad {q d₂ h f₅ f₇ : ℤ} (hq : 27 ≤ q) (hd₂ : 2 * d₂ = q * (q - 1))
    (hh : 2 * h = q - 1) (hf₅ : f₅ ≠ 0) (hf₇ : f₇ ≠ 0)
    (h17 : ((q ^ 3 * (q ^ 2 - 1) * (q ^ 2 - q - 1) : ℤ) : ℚ) *
      ((h : ℚ) ^ 2 * (-1) / d₂ + (q : ℚ) ^ 2 * 1 / ((2 * d₂ - 1 : ℤ) : ℚ) +
        ((q : ℚ) + 1) ^ 2 / (4 * f₅) + ((q : ℚ) + 1) ^ 2 / f₇) =
      -1 * q ^ 2 * (q ^ 2 - 1) * (q + 1) * (3 * q + 1))
    (hdeg : (-1) * d₂ + 1 * (2 * d₂ - 1) + f₅ + f₇ = 0) : False := by
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hq1 : (q : ℚ) ^ 2 - 1 ≠ 0 := by
    have : (q : ℤ) ^ 2 - 1 ≠ 0 := by nlinarith
    exact_mod_cast this
  have hqp : (q : ℚ) + 1 ≠ 0 := by
    have : (q + 1 : ℤ) ≠ 0 := by omega
    exact_mod_cast this
  have hN : (q : ℚ) ^ 2 - q - 1 ≠ 0 := by
    have : (q ^ 2 - q - 1 : ℤ) ≠ 0 := by nlinarith
    exact_mod_cast this
  have hf5 : (f₅ : ℚ) ≠ 0 := by exact_mod_cast hf₅
  have hf7 : (f₇ : ℚ) ≠ 0 := by exact_mod_cast hf₇
  have hN' : -1 - (q : ℚ) + (q : ℚ) ^ 2 ≠ 0 := by
    have : (-1 - q + q ^ 2 : ℤ) ≠ 0 := by nlinarith
    exact_mod_cast this
  have hd₂' : (d₂ : ℚ) = q * (q - 1) / 2 := by
    have : ((2 * d₂ : ℤ) : ℚ) = ((q * (q - 1) : ℤ) : ℚ) := by rw [hd₂]
    push_cast at this
    linarith
  have hh' : (h : ℚ) = (q - 1) / 2 := by
    have : ((2 * h : ℤ) : ℚ) = ((q - 1 : ℤ) : ℚ) := by rw [hh]
    push_cast at this
    linarith
  have hd4 : ((2 * d₂ - 1 : ℤ) : ℚ) = (q : ℚ) ^ 2 - q - 1 := by
    push_cast
    rw [hd₂']
    ring
  have hqm : (q : ℚ) - 1 ≠ 0 := by
    have : (q - 1 : ℤ) ≠ 0 := by omega
    exact_mod_cast this
  rw [hd4, hd₂', hh'] at h17
  push_cast at h17
  have hA1 : ((q : ℚ) ^ 3 * (q ^ 2 - 1) * (q ^ 2 - q - 1)) *
      ((((q : ℚ) - 1) / 2) ^ 2 * (-1) / (q * (q - 1) / 2)) =
      -q ^ 2 * (q ^ 2 - 1) * ((q ^ 2 - q - 1) * (q - 1) / 2) := by
    field_simp
  have hA2 : ((q : ℚ) ^ 3 * (q ^ 2 - 1) * (q ^ 2 - q - 1)) * ((q : ℚ) ^ 2 * 1 / (q ^ 2 - q - 1)) =
      q ^ 5 * (q ^ 2 - 1) := by
    rw [mul_div_assoc', show (q : ℚ) ^ 3 * (q ^ 2 - 1) * (q ^ 2 - q - 1) * (q ^ 2 * 1) =
      q ^ 5 * (q ^ 2 - 1) * (q ^ 2 - q - 1) by ring, mul_div_cancel_right₀ _ hN]
  have hB : ((q : ℚ) ^ 3 * (q ^ 2 - 1) * (q ^ 2 - q - 1)) *
      (((q : ℚ) + 1) ^ 2 / (4 * f₅) + ((q : ℚ) + 1) ^ 2 / f₇) =
      -q ^ 2 * (q ^ 2 - 1) * (q + 1) * (q ^ 2 + 7 * q + 1) / 2 := by
    linear_combination h17 - hA1 - hA2
  have hs : (f₇ : ℚ) = -(q - 2) * (q + 1) / 2 - f₅ := by
    have h1 : ((f₇ : ℤ) : ℚ) =
        (((-1) * d₂ + 1 * (2 * d₂ - 1) + f₅ + f₇ - (d₂ - 1) - f₅ : ℤ) : ℚ) := by
      push_cast; ring
    rw [hdeg] at h1
    push_cast at h1
    rw [h1, hd₂']
    ring
  have hquad : 4 * ((q : ℚ) ^ 2 + 7 * q + 1) * f₅ ^ 2 -
      4 * ((q + 1) * (q ^ 3 - 4 * q ^ 2 + 5 * q + 1)) * f₅ +
        q * (q + 1) ^ 2 * (q - 2) * (q ^ 2 - q - 1) = 0 := by
    field_simp at hB
    rw [hs] at hB
    linear_combination -hB
  have hid : (8 * ((q : ℚ) ^ 2 + 7 * q + 1) * f₅ -
      4 * ((q + 1) * (q ^ 3 - 4 * q ^ 2 + 5 * q + 1))) ^ 2 =
      16 * ((q + 1) ^ 2 * (q - 1) ^ 2 * (4 * q + 1) * (-3 * q ^ 2 + 6 * q + 1)) := by
    linear_combination (16 * ((q : ℚ) ^ 2 + 7 * q + 1)) * hquad
  have hneg :
      16 * (((q : ℚ) + 1) ^ 2 * (q - 1) ^ 2 * (4 * q + 1) * (-3 * q ^ 2 + 6 * q + 1)) < 0 := by
    have hq27 : (27 : ℚ) ≤ q := by exact_mod_cast hq
    have h1 : 0 < ((q : ℚ) + 1) ^ 2 * (q - 1) ^ 2 * (4 * q + 1) := by
      have : (0 : ℚ) < q - 1 := by linarith
      have : (0 : ℚ) < 4 * q + 1 := by linarith
      positivity
    have h2 : -3 * (q : ℚ) ^ 2 + 6 * q + 1 < 0 := by nlinarith
    nlinarith
  have hsq := sq_nonneg (8 * ((q : ℚ) ^ 2 + 7 * q + 1) * f₅ -
    4 * ((q + 1) * (q ^ 3 - 4 * q ^ 2 + 5 * q + 1)))
  rw [hid] at hsq
  linarith

theorem seven_four {q e a d₂ h : ℤ} (hq : 27 ≤ q) (he : IsSign e) (pd₂ : 0 < d₂)
    (hh : 2 * h = q - e) (pd₄ : 0 < 2 * d₂ - e)
    (h6 : ((q ^ 3 * (q ^ 2 - 1) * a : ℤ) : ℚ) *
      (1 + (h : ℚ) ^ 2 * (-e : ℤ) / d₂ + (h : ℚ) ^ 2 * (-e : ℤ) / d₂ +
        (q : ℚ) ^ 2 * (e : ℤ) / ((2 * d₂ - e : ℤ) : ℚ)) = q ^ 2 * (q ^ 2 - 1) ^ 2 * (q + e)) :
    q * a * (2 * d₂ + q - e) ^ 2 = (q ^ 2 - 1) * (q + e) * (2 * d₂) * (2 * d₂ - e) := by
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hd₂ : (d₂ : ℚ) ≠ 0 := by exact_mod_cast pd₂.ne'
  have hq1 : (q : ℚ) ^ 2 - 1 ≠ 0 := by
    have : (q : ℤ) ^ 2 - 1 ≠ 0 := by nlinarith
    exact_mod_cast this
  have hh' : (h : ℚ) = ((q : ℚ) - e) / 2 := by
    have : ((2 * h : ℤ) : ℚ) = ((q - e : ℤ) : ℚ) := by rw [hh]
    push_cast at this
    linarith
  rw [hh'] at h6
  rcases he with rfl | rfl
  · have hD4 : 2 * (d₂ : ℚ) - 1 ≠ 0 := by
      have : (2 * d₂ - 1 : ℤ) ≠ 0 := by omega
      exact_mod_cast this
    push_cast at h6
    field_simp at h6
    have key : ((q * a * (2 * d₂ + q - 1) ^ 2 : ℤ) : ℚ) =
        (((q ^ 2 - 1) * (q + 1) * (2 * d₂) * (2 * d₂ - 1) : ℤ) : ℚ) := by
      push_cast
      linear_combination h6 / 2
    exact_mod_cast key
  · have hD4 : 2 * (d₂ : ℚ) + 1 ≠ 0 := by
      have : (2 * d₂ + 1 : ℤ) ≠ 0 := by omega
      exact_mod_cast this
    push_cast at h6
    rw [show 2 * (d₂ : ℚ) - -1 = 2 * d₂ + 1 by ring] at h6
    field_simp at h6
    have key : ((q * a * (2 * d₂ + q - -1) ^ 2 : ℤ) : ℚ) =
        (((q ^ 2 - 1) * (q + -1) * (2 * d₂) * (2 * d₂ - -1) : ℤ) : ℚ) := by
      push_cast
      linear_combination h6 / 2
    exact_mod_cast key

theorem seven_arith {p m : ℕ} (hp : p.Prime) {q e a d₂ d₄ δ₂ δ₄ e₂ e₄ ν₂ f₅ f₇ h R : ℤ}
    (hqpm : q = (p : ℤ) ^ m) (hq : 27 ≤ q) (he : IsSign e) (hq8 : q % 8 = 4 + e) (ha : 0 < a)
    (h₂ : IsSign δ₂) (h₄ : IsSign δ₄)
    (hν : ν₂ = 0 ∨ ν₂ = 1 ∨ ν₂ = -1) (hνe : e = -1 → ν₂ = 0) (hνe' : e = 1 → ν₂ ≠ 0)
    (pd₂ : 0 < d₂) (pd₄ : 0 < d₄) (hf₅ : f₅ ≠ 0) (hf₇ : f₇ ≠ 0)
    (hh : 2 * h = q - e) (hR : 2 * R = q + e)
    (FS : 1 + ν₂ * δ₂ + ν₂ * δ₂ + δ₄ = 0) (O2 : δ₂ * e₂ + δ₄ * e₄ = 0)
    (R1 : 1 + δ₂ * e₂ + δ₂ * e₂ + δ₄ * e₄ = 0)
    (R3 : 1 + δ₂ * d₂ + δ₂ * d₂ + δ₄ * d₄ = 0)
    (h6 : ((q ^ 3 * (q ^ 2 - 1) * a : ℤ) : ℚ) *
      (1 + (h : ℚ) ^ 2 * δ₂ / d₂ + (h : ℚ) ^ 2 * δ₂ / d₂ + (q : ℚ) ^ 2 * δ₄ / d₄) =
      q ^ 2 * (q ^ 2 - 1) ^ 2 * (q + e))
    (hint : d₂ ∣ q ^ 2 * a * (-e * δ₂ * h)) (hRo : R ∣ d₄ - e₄)
    (h17 : ((q ^ 3 * (q ^ 2 - 1) * a : ℤ) : ℚ) *
      ((h : ℚ) ^ 2 * δ₂ / d₂ + (q : ℚ) ^ 2 * δ₄ / d₄ +
        ((q : ℚ) + e) ^ 2 / (4 * f₅) + ((q : ℚ) + e) ^ 2 / f₇) =
      -e * q ^ 2 * (q ^ 2 - 1) * (q + e) * (3 * q + e))
    (hdeg : δ₂ * d₂ + δ₄ * d₄ + f₅ + f₇ = 0) : False := by
  have hee := he.sq
  have hδ₄ : δ₄ = e := by
    rcases he with rfl | rfl
    · have hν0 := hνe' rfl
      rcases hν with h0 | h0 | h0
      · exact absurd h0 hν0
      · rw [h0] at FS
        rcases h₂ with rfl | rfl <;> rcases h₄ with rfl | rfl <;> omega
      · rw [h0] at FS
        rcases h₂ with rfl | rfl <;> rcases h₄ with rfl | rfl <;> omega
    · rw [hνe rfl] at FS
      linarith
  have h22 : δ₂ * e₂ = -1 := by linarith
  have h44 : δ₄ * e₄ = 1 := by linarith
  have he₄ : e₄ = e := by
    rw [hδ₄] at h44
    linear_combination e * h44 - e₄ * hee
  have hδ₂ : δ₂ = -e := by
    rw [hδ₄] at R3
    rcases he with rfl | rfl <;> rcases h₂ with rfl | rfl <;> first | rfl | (exfalso; linarith)
  have hd₄ : d₄ = 2 * d₂ - e := by
    rw [hδ₄, hδ₂] at R3
    linear_combination e * R3 + (2 * d₂ - d₄) * hee
  have h4 := seven_four (a := a) hq he pd₂ hh (by rw [← hd₄]; exact pd₄) (by
    rw [hδ₂, hδ₄, hd₄] at h6
    push_cast at h6 ⊢
    exact h6)
  have hint' : 2 * d₂ ∣ q ^ 2 * a * (q - e) := by
    rw [hδ₂] at hint
    have e1 : q ^ 2 * a * (-e * -e * h) = q ^ 2 * a * h := by linear_combination q ^ 2 * a * h * hee
    rw [e1] at hint
    have e2 : q ^ 2 * a * (q - e) = 2 * (q ^ 2 * a * h) := by rw [← hh]; ring
    rw [e2]
    exact mul_dvd_mul_left 2 hint
  have hRo' : R ∣ 2 * d₂ - 2 * e := by
    rw [hd₄, he₄] at hRo
    have : 2 * d₂ - e - e = 2 * d₂ - 2 * e := by ring
    rw [this] at hRo
    exact hRo
  obtain ⟨he1, hd, ha'⟩ :=
    seven_numth hp hqpm hq he hq8 ha (by omega) ⟨d₂, by ring⟩ h4 hint' hR hRo'
  subst he1
  have hδ₂' : δ₂ = -1 := hδ₂
  have hδ₄' : δ₄ = 1 := hδ₄
  have hd₄' : d₄ = 2 * d₂ - 1 := hd₄
  apply seven_quad (h := h) (f₅ := f₅) (f₇ := f₇) hq hd (by linarith) hf₅ hf₇
  · rw [hδ₂', hδ₄', hd₄', ha'] at h17
    push_cast at h17 ⊢
    exact h17
  · rw [hδ₂', hδ₄', hd₄'] at hdeg
    exact hdeg

end CFSG.Walter.Ward
