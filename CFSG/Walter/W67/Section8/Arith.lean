module

public import CFSG.Walter.W67.Interface

public section

namespace CFSG.Walter.W67

namespace Section8

theorem no_int_root_eps_one (q x : ℤ) (hq : 27 ≤ q)
    (h : q * (x - q) ^ 2 + (q ^ 2 - 1) ^ 2 * x = 0) : False := by
  set B := q ^ 4 - 4 * q ^ 2 + 1 with hB
  have hh : q * x ^ 2 + B * x + q ^ 3 = 0 := by rw [hB]; linear_combination h
  have hB0 : 0 < B := by rw [hB]; nlinarith [sq_nonneg (q ^ 2 - 4)]
  rcases le_or_gt 0 x with hx | hx
  · nlinarith [sq_nonneg x, mul_nonneg hB0.le hx, pow_pos (by linarith : (0:ℤ) < q) 3]
  set x₀ := -q ^ 3 + 4 * q with hx₀
  have hval0 : q * x₀ ^ 2 + B * x₀ + q ^ 3 = 4 * q := by rw [hx₀, hB]; ring
  rcases le_or_gt x x₀ with hle | hlt
  · have hid : q * x ^ 2 + B * x + q ^ 3 =
        (q * x₀ ^ 2 + B * x₀ + q ^ 3) + (x - x₀) * (q * (x + x₀) + B) := by ring
    have hneg : q * (x + x₀) + B < 0 := by
      have : q * (x + x₀) ≤ q * (2 * x₀) := by nlinarith
      have : q * (2 * x₀) + B < 0 := by
        rw [hx₀, hB]; nlinarith [pow_pos (by linarith : (0:ℤ) < q) 2]
      linarith
    nlinarith [mul_nonneg (sub_nonneg.2 hle) (neg_nonneg.2 hneg.le)]
  · set a := x₀ + 1 with ha
    have hax : a ≤ x := by omega
    have hxb : x ≤ -1 := by omega
    have hva : q * a ^ 2 + B * a + q ^ 3 = -q ^ 4 + 4 * q ^ 2 + 5 * q + 1 := by
      rw [ha, hx₀, hB]; ring
    have hvb : q * (-1) ^ 2 + B * (-1) + q ^ 3 = -(q + 1) ^ 2 * (q ^ 2 - 3 * q + 1) := by
      rw [hB]; ring
    have hva' : q * a ^ 2 + B * a + q ^ 3 < 0 := by
      rw [hva]
      nlinarith [pow_pos (by linarith : (0:ℤ) < q) 2, pow_pos (by linarith : (0:ℤ) < q) 3]
    have hvb' : q * (-1) ^ 2 + B * (-1) + q ^ 3 < 0 := by
      rw [hvb]; nlinarith [sq_nonneg (q + 1), pow_pos (by linarith : (0:ℤ) < q) 2]
    have hid : (-1 - a) * (q * x ^ 2 + B * x + q ^ 3) =
        (-1 - x) * (q * a ^ 2 + B * a + q ^ 3) + (x - a) * (q * (-1) ^ 2 + B * (-1) + q ^ 3)
          + q * (-1 - a) * ((x - a) * (x - (-1))) := by ring
    have hba : 0 < -1 - a := by
      rw [ha, hx₀]; nlinarith [pow_pos (by linarith : (0:ℤ) < q) 2]
    have h1 : (-1 - x) * (q * a ^ 2 + B * a + q ^ 3) +
        (x - a) * (q * (-1) ^ 2 + B * (-1) + q ^ 3) < 0 := by
      rcases eq_or_lt_of_le hax with heq | hlt'
      · rw [← heq]; nlinarith
      · nlinarith [mul_neg_of_pos_of_neg (sub_pos.2 hlt') hvb',
          mul_nonpos_of_nonneg_of_nonpos (by linarith : (0:ℤ) ≤ -1 - x) hva'.le]
    have h2 : q * (-1 - a) * ((x - a) * (x - (-1))) ≤ 0 := by
      apply mul_nonpos_of_nonneg_of_nonpos
      · positivity
      · nlinarith
    have : (-1 - a) * (q * x ^ 2 + B * x + q ^ 3) < 0 := by rw [hid]; linarith
    rw [hh, mul_zero] at this
    exact lt_irrefl _ this

theorem no_int_root_eps (q v : ℤ) (hq : 27 ≤ q)
    (h : (q ^ 2 - 3 * q + 1) * v ^ 2 + (q ^ 2 - q + 1) * (q ^ 3 - 3 * q ^ 2 - q + 1) * v
      - q ^ 3 * (q ^ 2 - q + 1) ^ 2 = 0) : False := by
  set f : ℤ → ℤ := fun w => (q ^ 2 - 3 * q + 1) * w ^ 2 +
    (q ^ 2 - q + 1) * (q ^ 3 - 3 * q ^ 2 - q + 1) * w - q ^ 3 * (q ^ 2 - q + 1) ^ 2 with hf
  have hfv : f v = 0 := h
  have hq0 : (0:ℤ) < q := by linarith
  have hq2 := pow_pos hq0 2
  have hq3 := pow_pos hq0 3
  have hq4 := pow_pos hq0 4
  have hd0 : 0 < q ^ 2 - 3 * q + 1 := by nlinarith
  have hcP : 0 < (q ^ 2 - q + 1) * (q ^ 3 - 3 * q ^ 2 - q + 1) := by
    apply mul_pos <;> nlinarith
  have hdiff : ∀ w w', f w - f w' = (w - w') * ((q ^ 2 - 3 * q + 1) * (w + w') +
      (q ^ 2 - q + 1) * (q ^ 3 - 3 * q ^ 2 - q + 1)) := by
    intro w w'; simp only [hf]; ring
  have hfb : f (q ^ 2 + q + 5) = -2 * (5 * q ^ 4 + 5 * q ^ 3 + 37 * q - 15) := by
    simp only [hf]; ring
  have hfb' : f (q ^ 2 + q + 6) =
      q ^ 5 - 12 * q ^ 4 - 11 * q ^ 3 + 6 * q ^ 2 - 107 * q + 42 := by
    simp only [hf]; ring
  have hfa : f (-(q ^ 3 + 2)) = -2 * (2 * q ^ 3 - 3 * q ^ 2 + 4 * q - 1) := by
    simp only [hf]; ring
  have hfa' : f (-(q ^ 3 + 3)) = q ^ 5 - 2 * q ^ 4 - 5 * q ^ 3 + 12 * q ^ 2 - 21 * q + 6 := by
    simp only [hf]; ring
  have sb : f (q ^ 2 + q + 5) < 0 := by rw [hfb]; nlinarith
  have sb' : 0 < f (q ^ 2 + q + 6) := by
    rw [hfb']; nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ q - 27) hq4.le]
  have sa : f (-(q ^ 3 + 2)) < 0 := by rw [hfa]; nlinarith
  have sa' : 0 < f (-(q ^ 3 + 3)) := by
    rw [hfa']; nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ q - 27) hq4.le]
  rcases le_or_gt (q ^ 2 + q + 6) v with h1 | h1
  · have := hdiff v (q ^ 2 + q + 6)
    have hpos : 0 ≤ (v - (q ^ 2 + q + 6)) * ((q ^ 2 - 3 * q + 1) * (v + (q ^ 2 + q + 6)) +
        (q ^ 2 - q + 1) * (q ^ 3 - 3 * q ^ 2 - q + 1)) := by
      apply mul_nonneg (by linarith)
      have : 0 ≤ (q ^ 2 - 3 * q + 1) * (v + (q ^ 2 + q + 6)) := mul_nonneg hd0.le (by nlinarith)
      linarith
    linarith
  rcases le_or_gt v (-(q ^ 3 + 3)) with h2 | h2
  · have := hdiff v (-(q ^ 3 + 3))
    have hneg : (q ^ 2 - 3 * q + 1) * (v + -(q ^ 3 + 3)) +
        (q ^ 2 - q + 1) * (q ^ 3 - 3 * q ^ 2 - q + 1) < 0 := by
      have h3 : (q ^ 2 - 3 * q + 1) * (v + -(q ^ 3 + 3)) ≤
          (q ^ 2 - 3 * q + 1) * (2 * -(q ^ 3 + 3)) :=
        mul_le_mul_of_nonneg_left (by linarith) hd0.le
      have h4 : (q ^ 2 - 3 * q + 1) * (2 * -(q ^ 3 + 3)) +
          (q ^ 2 - q + 1) * (q ^ 3 - 3 * q ^ 2 - q + 1) < 0 := by
        nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ q - 27) hq4.le]
      linarith
    have hpos : 0 ≤ (v - -(q ^ 3 + 3)) * ((q ^ 2 - 3 * q + 1) * (v + -(q ^ 3 + 3)) +
        (q ^ 2 - q + 1) * (q ^ 3 - 3 * q ^ 2 - q + 1)) :=
      mul_nonneg_of_nonpos_of_nonpos (by linarith) hneg.le
    linarith
  have hav : -(q ^ 3 + 2) ≤ v := by omega
  have hvb : v ≤ q ^ 2 + q + 5 := by omega
  set a := -(q ^ 3 + 2) with ha
  set b := q ^ 2 + q + 5 with hb
  have hid : (b - a) * f v = (b - v) * f a + (v - a) * f b +
      (q ^ 2 - 3 * q + 1) * (b - a) * ((v - a) * (v - b)) := by
    simp only [hf]; ring
  have hab : 0 < b - a := by rw [ha, hb]; nlinarith
  have h1' : (b - v) * f a + (v - a) * f b < 0 := by
    rcases eq_or_lt_of_le hav with heq | hlt
    · rw [← heq]; nlinarith
    · nlinarith [mul_neg_of_pos_of_neg (sub_pos.2 hlt) sb,
        mul_nonpos_of_nonneg_of_nonpos (by linarith : (0:ℤ) ≤ b - v) sa.le]
  have h2' : (q ^ 2 - 3 * q + 1) * (b - a) * ((v - a) * (v - b)) ≤ 0 := by
    apply mul_nonpos_of_nonneg_of_nonpos
    · exact mul_nonneg hd0.le hab.le
    · nlinarith
  have : (b - a) * f v < 0 := by rw [hid]; linarith
  rw [hfv, mul_zero] at this
  exact lt_irrefl _ this

theorem not_dvd_mod8 (q : ℕ) (hq8 : q % 8 = 3) :
    ¬ (8 : ℤ) ∣ (q : ℤ) * ((q : ℤ) ^ 2 - q + 1) + 7 := by
  rintro ⟨m, hm⟩
  obtain ⟨k, rfl⟩ : ∃ k, q = 8 * k + 3 := ⟨q / 8, by omega⟩
  push_cast at hm
  have h : (8 : ℤ) * (m - (64 * k ^ 3 + 64 * k ^ 2 + 22 * k + 3)) = 4 := by
    linear_combination -hm
  omega

end Section8

namespace CTData

variable {q e g : ℕ} (d : CTData q e g)

theorem ε_ne_zero (l : d.ι) : d.ε l ≠ 0 := by
  rcases d.ε_sq l with h | h <;> simp [h]

theorem ε_mul_self (l : d.ι) : d.ε l * d.ε l = 1 := by
  rcases d.ε_sq l with h | h <;> simp [h]

theorem x4'_eq (l : d.ι) : d.x4' l = (q : ℤ) * d.x1' l := by
  obtain ⟨-, h1', -, h4', hα⟩ := d.ne_zero l
  have h816 := d.r816 l
  have h818 := d.r818 l
  have hA : (d.x1' l : ℚ) ≠ 0 := by exact_mod_cast h1'
  have hB : (d.x4' l : ℚ) ≠ 0 := by exact_mod_cast h4'
  have hε' : (d.ε l : ℚ) ≠ 0 := by exact_mod_cast d.ε_ne_zero l
  have hα' : (d.xα l : ℚ) ≠ 0 := by exact_mod_cast hα
  have hC : ((d.ε l : ℚ) * d.xα l) ≠ 0 := mul_ne_zero hε' hα'
  have hCe : ((d.ε l : ℚ) * d.xα l) = d.x4' l - d.x1' l := by
    have : (d.ε l * d.xα l : ℤ) = d.x4' l - d.x1' l := by linarith
    exact_mod_cast this
  have h2 : (d.x4' l : ℚ) * ((d.ε l : ℚ) * d.xα l) -
      (q : ℚ) ^ 2 * d.x1' l * ((d.ε l : ℚ) * d.xα l) +
      ((q : ℚ) - 1) ^ 2 * d.x1' l * d.x4' l = 0 := by
    have := congrArg (· * ((d.x1' l : ℚ) * d.x4' l * ((d.ε l : ℚ) * d.xα l))) h818
    simp only [zero_mul] at this
    rw [← this]
    field_simp
  rw [hCe] at h2
  have h3 : ((d.x4' l : ℚ) - q * d.x1' l) ^ 2 = 0 := by linear_combination h2
  have h4 : (d.x4' l : ℚ) = q * d.x1' l := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h3
    linarith
  exact_mod_cast h4

theorem x1_add_x4 (l : d.ι) : d.x1 l + d.x4 l = ((q : ℤ) + 1) * d.x1' l := by
  have := d.r83 l
  rw [d.x4'_eq l] at this
  linarith

theorem ε_mul_g (l : d.ι) :
    d.ε l * (g : ℤ) = (q : ℤ) ^ 3 * ((q : ℤ) ^ 2 - 1) * e * d.x1' l := by
  have h816 := d.r816 l
  rw [d.x4'_eq l] at h816
  have hεα : d.ε l * d.xα l = ((q : ℤ) - 1) * d.x1' l := by linarith
  rw [d.r813 l]
  linear_combination (q : ℤ) ^ 3 * ((q : ℤ) + 1) * e * hεα

theorem r86_cleared (l : d.ι) :
    (g : ℤ) * (d.x4 l * d.x1' l + (q : ℤ) ^ 2 * d.x1 l * d.x1' l -
      ((q : ℤ) + 1) * d.x1 l * d.x4 l) =
    (q : ℤ) ^ 2 * ((q : ℤ) - 1) ^ 3 * ((q : ℤ) + 1) ^ 2 * e * (d.x1 l * d.x4 l * d.x1' l) := by
  obtain ⟨h1, h1', h4, -, -⟩ := d.ne_zero l
  have h86 := d.r86 l
  have h4' : (d.x4' l : ℚ) = q * d.x1' l := by exact_mod_cast d.x4'_eq l
  rw [h4'] at h86
  have hu : (d.x1 l : ℚ) ≠ 0 := by exact_mod_cast h1
  have hX : (d.x1' l : ℚ) ≠ 0 := by exact_mod_cast h1'
  have hv : (d.x4 l : ℚ) ≠ 0 := by exact_mod_cast h4
  have hq : (q : ℚ) ≠ 0 := by
    intro hq0
    have : ((d.x4' l : ℤ) : ℚ) = 0 := by rw [h4', hq0, zero_mul]
    exact (d.ne_zero l).2.2.2.1 (by exact_mod_cast this)
  have key : ((g : ℤ) : ℚ) * (d.x4 l * d.x1' l + (q : ℚ) ^ 2 * d.x1 l * d.x1' l -
      ((q : ℚ) + 1) * d.x1 l * d.x4 l) =
      (q : ℚ) ^ 2 * ((q : ℚ) - 1) ^ 3 * ((q : ℚ) + 1) ^ 2 * e * (d.x1 l * d.x4 l * d.x1' l) := by
    have := congrArg (· * ((d.x1 l : ℚ) * d.x4 l * d.x1' l)) h86
    rw [← this]
    push_cast
    field_simp
    ring
  exact_mod_cast key

theorem principal_facts (hq : 27 ≤ q) :
    d.x4 d.l₀ = (q : ℤ) ^ 3 ∧ d.x1' d.l₀ = (q : ℤ) ^ 2 - q + 1 ∧ d.ε d.l₀ = 1 ∧
      (g : ℤ) = (q : ℤ) ^ 3 * ((q : ℤ) ^ 2 - 1) * ((q : ℤ) ^ 2 - q + 1) * e := by
  have hq' : (27 : ℤ) ≤ q := by exact_mod_cast hq
  have hu : d.x1 d.l₀ = 1 := d.x1_l₀
  obtain ⟨-, hX0, -, -, -⟩ := d.ne_zero d.l₀
  have hsum : 1 + d.x4 d.l₀ = ((q : ℤ) + 1) * d.x1' d.l₀ := by
    have := d.x1_add_x4 d.l₀
    rwa [hu] at this
  have hεg := d.ε_mul_g d.l₀
  have h86 := d.r86_cleared d.l₀
  rw [hu] at h86
  have he0 : (e : ℤ) ≠ 0 := by
    have : 0 < e := by rw [← d.card_ι]; exact Fintype.card_pos_iff.mpr ⟨d.l₀⟩
    exact_mod_cast this.ne'
  have hne : (q : ℤ) ^ 2 * ((q : ℤ) ^ 2 - 1) * e * d.x1' d.l₀ ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (by positivity) ?_) he0) hX0
    nlinarith
  have E2 : ((q : ℤ) ^ 2 * ((q : ℤ) ^ 2 - 1) * e * d.x1' d.l₀) *
      ((q : ℤ) * (d.x4 d.l₀ * d.x1' d.l₀ + (q : ℤ) ^ 2 * d.x1' d.l₀ -
        ((q : ℤ) + 1) * d.x4 d.l₀)) =
      ((q : ℤ) ^ 2 * ((q : ℤ) ^ 2 - 1) * e * d.x1' d.l₀) *
        (d.ε d.l₀ * ((q : ℤ) - 1) ^ 2 * ((q : ℤ) + 1) * d.x4 d.l₀) := by
    linear_combination d.ε d.l₀ * h86 -
      (d.x4 d.l₀ * d.x1' d.l₀ + (q : ℤ) ^ 2 * 1 * d.x1' d.l₀ -
        ((q : ℤ) + 1) * 1 * d.x4 d.l₀) * hεg
  have E3 := mul_left_cancel₀ hne E2
  have E4 : (q : ℤ) * (d.x4 d.l₀ - q) ^ 2 =
      d.ε d.l₀ * ((q : ℤ) ^ 2 - 1) ^ 2 * d.x4 d.l₀ := by
    linear_combination ((q : ℤ) + 1) * E3 + (q : ℤ) * (d.x4 d.l₀ + (q : ℤ) ^ 2) * hsum
  rcases d.ε_sq d.l₀ with h1 | h1
  · rw [h1, one_mul] at E4
    have hfac : (d.x4 d.l₀ - (q : ℤ) ^ 3) * ((q : ℤ) * d.x4 d.l₀ - 1) = 0 := by
      linear_combination E4
    have hqx : (q : ℤ) * d.x4 d.l₀ - 1 ≠ 0 := by
      intro h0
      rcases le_or_gt (d.x4 d.l₀) 0 with hx' | hx'
      · nlinarith
      · nlinarith
    have hx3 : d.x4 d.l₀ = (q : ℤ) ^ 3 := by
      have := (mul_eq_zero.mp hfac).resolve_right hqx
      linarith
    have hX3 : d.x1' d.l₀ = (q : ℤ) ^ 2 - q + 1 := by
      have hq1 : ((q : ℤ) + 1) ≠ 0 := by positivity
      apply mul_left_cancel₀ hq1
      rw [← hsum, hx3]
      ring
    refine ⟨hx3, hX3, h1, ?_⟩
    rw [h1, one_mul] at hεg
    rw [hεg, hX3]
    ring
  · exfalso
    rw [h1] at E4
    exact Section8.no_int_root_eps_one q (d.x4 d.l₀) hq' (by linear_combination E4)

theorem eq_l₀ (hq8 : q % 8 = 3) (hq : 27 ≤ q) (l : d.ι) : l = d.l₀ := by
  by_contra hl
  have hq' : (27 : ℤ) ≤ q := by exact_mod_cast hq
  obtain ⟨-, -, -, hg⟩ := d.principal_facts hq
  have hεε : d.ε l * d.ε l = 1 := d.ε_mul_self l
  have he0 : (e : ℤ) ≠ 0 := by
    have : 0 < e := by rw [← d.card_ι]; exact Fintype.card_pos_iff.mpr ⟨d.l₀⟩
    exact_mod_cast this.ne'
  have hc0 : (q : ℤ) ^ 2 - q + 1 ≠ 0 := by nlinarith
  have hq2 : (q : ℤ) ^ 2 - 1 ≠ 0 := by nlinarith
  have hX : d.x1' l = d.ε l * ((q : ℤ) ^ 2 - q + 1) := by
    have h1 := d.ε_mul_g l
    rw [hg] at h1
    have hne : (q : ℤ) ^ 3 * ((q : ℤ) ^ 2 - 1) * e ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by positivity) hq2) he0
    apply mul_left_cancel₀ hne
    linear_combination -h1
  have hsum : d.x1 l + d.x4 l = d.ε l * ((q : ℤ) + 1) * ((q : ℤ) ^ 2 - q + 1) := by
    rw [d.x1_add_x4 l, hX]; ring
  have h86 := d.r86_cleared l
  rw [hg, hX] at h86
  have hne2 : (q : ℤ) ^ 2 * ((q : ℤ) ^ 2 - 1) * ((q : ℤ) ^ 2 - q + 1) * e ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (by positivity) hq2) hc0) he0
  have E1 : ((q : ℤ) ^ 2 * ((q : ℤ) ^ 2 - 1) * ((q : ℤ) ^ 2 - q + 1) * e) *
      ((q : ℤ) * ((q : ℤ) ^ 2 - q + 1) * (d.x4 l + (q : ℤ) ^ 2 * d.x1 l)) =
      ((q : ℤ) ^ 2 * ((q : ℤ) ^ 2 - 1) * ((q : ℤ) ^ 2 - q + 1) * e) *
        (((q : ℤ) + 1) * d.x1 l * d.x4 l * (((q : ℤ) - 1) ^ 2 + d.ε l * q)) := by
    linear_combination d.ε l * h86 -
      ((q : ℤ) ^ 3 * ((q : ℤ) ^ 2 - 1) * ((q : ℤ) ^ 2 - q + 1) ^ 2 * e *
          (d.x4 l + (q : ℤ) ^ 2 * d.x1 l) -
        (q : ℤ) ^ 2 * ((q : ℤ) - 1) ^ 3 * ((q : ℤ) + 1) ^ 2 * ((q : ℤ) ^ 2 - q + 1) * e *
          d.x1 l * d.x4 l) * hεε
  have E2 := mul_left_cancel₀ hne2 E1
  rcases d.ε_sq l with h1 | h1
  ·
    rw [h1] at E2 hsum
    have E3 : (q : ℤ) * (d.x4 l + (q : ℤ) ^ 2 * d.x1 l) = ((q : ℤ) + 1) * d.x1 l * d.x4 l := by
      apply mul_left_cancel₀ hc0
      linear_combination E2
    have hfac : ((q : ℤ) + 1) * ((d.x1 l - 1) * (d.x1 l - q * ((q : ℤ) ^ 2 - q + 1))) = 0 := by
      linear_combination E3 - ((q : ℤ) - ((q : ℤ) + 1) * d.x1 l) * hsum
    rcases mul_eq_zero.mp hfac with h0 | h0
    · have : (0 : ℤ) < (q : ℤ) + 1 := by positivity
      linarith
    rcases mul_eq_zero.mp h0 with h0 | h0
    · exact (d.nonlinear l hl).1 (by linarith)
    · have h8 := d.mod8 l
      rw [show d.x1 l = (q : ℤ) * ((q : ℤ) ^ 2 - q + 1) by linarith] at h8
      exact Section8.not_dvd_mod8 q hq8 h8
  ·
    rw [h1] at E2 hsum
    have key : ((q : ℤ) + 1) * ((q ^ 2 - 3 * q + 1) * d.x4 l ^ 2 +
        (q ^ 2 - q + 1) * (q ^ 3 - 3 * q ^ 2 - q + 1) * d.x4 l - q ^ 3 * (q ^ 2 - q + 1) ^ 2)
        = 0 := by
      linear_combination E2 - ((q : ℤ) ^ 3 * ((q : ℤ) ^ 2 - q + 1) -
        ((q : ℤ) + 1) * ((q : ℤ) ^ 2 - 3 * q + 1) * d.x4 l) * hsum
    have hq1 : ((q : ℤ) + 1) ≠ 0 := by positivity
    exact Section8.no_int_root_eps q (d.x4 l) hq'
      ((mul_eq_zero.mp key).resolve_left hq1)

end CTData

theorem ctData_arith :
    ∀ {q e g : ℕ}, CTData q e g → q % 8 = 3 → 27 ≤ q →
      e = 1 ∧ g = q ^ 3 * (q ^ 3 + 1) * (q - 1) := by
  intro q e g d hq8 hq
  have hall : ∀ l, l = d.l₀ := d.eq_l₀ hq8 hq
  have he : e = 1 := by
    rw [← d.card_ι]
    exact Fintype.card_eq_one_iff.mpr ⟨d.l₀, hall⟩
  refine ⟨he, ?_⟩
  obtain ⟨-, -, -, hg⟩ := d.principal_facts hq
  subst he
  have h1 : 1 ≤ q := by omega
  have : (g : ℤ) = ((q ^ 3 * (q ^ 3 + 1) * (q - 1) : ℕ) : ℤ) := by
    rw [hg]
    push_cast [Nat.cast_sub h1]
    ring
  exact_mod_cast this

end CFSG.Walter.W67
