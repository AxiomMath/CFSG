module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Data.Rat.Star
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Walter.Ward

@[expose] def IsSign (δ : ℤ) : Prop := δ = 1 ∨ δ = -1

theorem IsSign.sq {δ : ℤ} (h : IsSign δ) : δ * δ = 1 := by rcases h with rfl | rfl <;> norm_num

theorem IsSign.ne_zero {δ : ℤ} (h : IsSign δ) : δ ≠ 0 := by rcases h with rfl | rfl <;> norm_num

theorem IsSign.mul {a b : ℤ} (ha : IsSign a) (hb : IsSign b) : IsSign (a * b) := by
  unfold IsSign
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num

theorem IsSign.neg {a : ℤ} (ha : IsSign a) : IsSign (-a) := by
  unfold IsSign
  rcases ha with rfl | rfl <;> norm_num

theorem IsSign.one : IsSign 1 := Or.inl rfl

theorem eight_signs {q e g d₂ d₃ d₄ δ₂ δ₃ δ₄ e₂ e₃ e₄ D : ℤ} (hq : 27 ≤ q) (he : IsSign e)
    (h₂ : IsSign δ₂) (h₃ : IsSign δ₃) (h₄ : IsSign δ₄) (pd₂ : 0 < d₂) (pd₃ : 0 < d₃)
    (pd₄ : 0 < d₄) (hD : D ≠ 0) (hg : g ≠ 0)
    (h6 : (g : ℚ) * (1 + δ₂ / d₂ + δ₃ * q ^ 2 / d₃ + δ₄ * q ^ 2 / d₄) =
      q ^ 2 * (q ^ 2 - 1) ^ 2 * (q + e))
    (h8 : ((q : ℚ) + e) * (q * (q ^ 2 - 1)) ^ 2 =
      g * (2 * (q - e) ^ 2 * e / D + 1 + e₂ / d₂ + e₃ * q ^ 2 / d₃ + e₄ * q ^ 2 / d₄))
    (R1 : 1 + δ₂ * e₂ + δ₃ * e₃ + δ₄ * e₄ = 0)
    (R2 : 2 * e * D + 1 + e₂ * d₂ + e₃ * d₃ + e₄ * d₄ = 0)
    (R3 : 1 + δ₂ * d₂ + δ₃ * d₃ + δ₄ * d₄ = 0)
    (O2 : δ₃ * e₃ + δ₄ * e₄ = 0) (hσ : δ₃ = e₃) :
    e₂ = -δ₂ ∧ e₄ = -δ₄ ∧ δ₃ = e * δ₂ ∧ δ₄ = -e * δ₂ ∧ d₄ = q * d₂ ∧
      d₃ = (q - e) * d₂ - e * δ₂ := by
  have hee := he.sq
  have h22 := h₂.sq
  have h33 := h₃.sq
  have h44 := h₄.sq
  have he₄ : e₄ = -δ₄ := by
    rw [← hσ, h33] at O2
    have h1 : δ₄ * e₄ = -1 := by linarith
    linear_combination δ₄ * h1 - e₄ * h44
  have he₂ : e₂ = -δ₂ := by
    rw [← hσ, h33, he₄] at R1
    have h1 : δ₂ * e₂ = -1 := by linear_combination R1 + h44
    linear_combination δ₂ * h1 - e₂ * h22
  have heD : e * D = δ₂ * d₂ + δ₄ * d₄ := by
    rw [he₂, ← hσ, he₄] at R2
    have h2 : 2 * (e * D) = 2 * (δ₂ * d₂ + δ₄ * d₄) := by linear_combination R2 - R3
    linarith
  have hg' : (g : ℚ) ≠ 0 := by exact_mod_cast hg
  have hd₂ : (d₂ : ℚ) ≠ 0 := by exact_mod_cast pd₂.ne'
  have hd₃ : (d₃ : ℚ) ≠ 0 := by exact_mod_cast pd₃.ne'
  have hd₄ : (d₄ : ℚ) ≠ 0 := by exact_mod_cast pd₄.ne'
  have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast hD
  have hδ₂ : (δ₂ : ℚ) ≠ 0 := by exact_mod_cast h₂.ne_zero
  have hδ₄ : (δ₄ : ℚ) ≠ 0 := by exact_mod_cast h₄.ne_zero
  have he0 : (e : ℚ) ≠ 0 := by exact_mod_cast he.ne_zero
  have hee' : (e : ℚ) * e = 1 := by exact_mod_cast hee
  have h22' : (δ₂ : ℚ) * δ₂ = 1 := by exact_mod_cast h22
  have h44' : (δ₄ : ℚ) * δ₄ = 1 := by exact_mod_cast h44
  have h9 : ((δ₂ : ℚ) / d₂ + δ₄ * q ^ 2 / d₄) = (q - e) ^ 2 * e / D := by
    have hXY : (1 + (δ₂ : ℚ) / d₂ + δ₃ * q ^ 2 / d₃ + δ₄ * q ^ 2 / d₄) =
        2 * (q - e) ^ 2 * e / D + 1 + e₂ / d₂ + e₃ * q ^ 2 / d₃ + e₄ * q ^ 2 / d₄ := by
      apply mul_left_cancel₀ hg'
      rw [h6, ← h8]
      ring
    rw [he₂, ← hσ, he₄] at hXY
    push_cast at hXY
    linear_combination hXY / 2
  have heD' : (e : ℚ) * D = δ₂ * d₂ + δ₄ * d₄ := by exact_mod_cast heD
  have huw : (δ₂ : ℚ) * d₂ + δ₄ * d₄ ≠ 0 := by rw [← heD']; exact mul_ne_zero he0 hD'
  have key : ((q * (δ₂ * d₂) + e * (δ₄ * d₄) : ℤ) : ℚ) ^ 2 = 0 := by
    have hD'' : (D : ℚ) = e * (δ₂ * d₂ + δ₄ * d₄) := by
      rw [← heD']; linear_combination -(D : ℚ) * hee'
    rw [hD''] at h9
    field_simp at h9
    push_cast
    linear_combination ((δ₂ : ℚ) * δ₄) * h9 +
      (-(q : ℚ) ^ 2 * δ₂ ^ 2 * d₂ ^ 2 - δ₂ * δ₄ * q ^ 2 * d₂ * d₄) * h44' +
      (-(δ₄ : ℚ) ^ 2 * d₄ ^ 2 - δ₂ * δ₄ * d₂ * d₄) * h22' +
      ((δ₄ : ℚ) ^ 2 * d₄ ^ 2 + δ₂ * δ₄ * d₂ * d₄) * hee'
  have hk : q * (δ₂ * d₂) + e * (δ₄ * d₄) = 0 := by
    have := (pow_eq_zero_iff (n := 2) (by norm_num)).mp key
    exact_mod_cast this
  have hw' : δ₄ * d₄ = -e * q * (δ₂ * d₂) := by linear_combination e * hk - (δ₄ * d₄) * hee
  have hv : 1 + δ₃ * d₃ = (e * q - 1) * (δ₂ * d₂) := by linear_combination R3 - hw'
  have hqd : 0 < q * d₂ := by positivity
  refine ⟨he₂, he₄, ?_⟩
  have hc : IsSign (-e * δ₂ * δ₄) := (he.neg.mul h₂).mul h₄
  have hd4c : d₄ = (-e * δ₂ * δ₄) * (q * d₂) := by
    linear_combination δ₄ * hw' - d₄ * h44
  have hc1 : -e * δ₂ * δ₄ = 1 := by
    rcases hc with h | h
    · exact h
    · rw [h] at hd4c; linarith
  have hδ4 : δ₄ = -e * δ₂ := by linear_combination (-δ₄) * hc1 - (e * δ₂) * h44
  have hc' : IsSign (e * δ₂ * δ₃) := (he.mul h₂).mul h₃
  have hd3c : (e * δ₂ * δ₃) * d₃ = (q - e) * d₂ - e * δ₂ := by
    linear_combination (e * δ₂) * hv + (d₂ * q * e ^ 2 - e * d₂) * h22 + (d₂ * q) * hee
  have hc'1 : e * δ₂ * δ₃ = 1 := by
    rcases hc' with h | h
    · exact h
    · exfalso
      rw [h] at hd3c
      have heδ : -1 ≤ e * δ₂ ∧ e * δ₂ ≤ 1 := by
        rcases (he.mul h₂) with h' | h' <;> rw [h'] <;> norm_num
      have hqe : 26 ≤ q - e := by rcases he with h' | h' <;> rw [h'] <;> omega
      nlinarith
  have hδ3 : δ₃ = e * δ₂ := by linear_combination (-δ₃) * hc'1 + (e * δ₂) * h33
  refine ⟨hδ3, hδ4, ?_, ?_⟩
  · rw [hc1, one_mul] at hd4c; exact hd4c
  · rw [hc'1, one_mul] at hd3c; exact hd3c

theorem eight_ten {q e a d₂ : ℤ} (hq : 27 ≤ q) (he : IsSign e) (pd₂ : 0 < d₂)
    (pd₃ : 0 < (q - e) * d₂ + e)
    (h6 : ((q ^ 3 * (q ^ 2 - 1) * a : ℤ) : ℚ) *
      (1 + (-1 : ℤ) / d₂ + (-e : ℤ) * q ^ 2 / (((q - e) * d₂ + e : ℤ) : ℚ) +
        (e : ℤ) * q ^ 2 / ((q * d₂ : ℤ) : ℚ)) = q ^ 2 * (q ^ 2 - 1) ^ 2 * (q + e)) :
    q * a * (d₂ - 1) ^ 2 = (q + e) ^ 2 * d₂ * ((q - e) * d₂ + e) := by
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hd₂ : (d₂ : ℚ) ≠ 0 := by exact_mod_cast pd₂.ne'
  have hq1 : (q : ℚ) ^ 2 - 1 ≠ 0 := by
    have : (q : ℤ) ^ 2 - 1 ≠ 0 := by nlinarith
    exact_mod_cast this
  rcases he with rfl | rfl
  · have hD3 : (d₂ : ℚ) * (q - 1) + 1 ≠ 0 := by
      have : (d₂ * (q - 1) + 1 : ℤ) ≠ 0 := by nlinarith
      exact_mod_cast this
    have hqe : (q : ℚ) - 1 ≠ 0 := by
      have : (q : ℤ) - 1 ≠ 0 := by omega
      exact_mod_cast this
    push_cast at h6
    rw [show ((q : ℚ) - 1) * d₂ + 1 = d₂ * (q - 1) + 1 by ring] at h6
    field_simp at h6
    have key : ((q * a * (d₂ - 1) ^ 2 : ℤ) : ℚ) =
        (((q + 1) ^ 2 * d₂ * ((q - 1) * d₂ + 1) : ℤ) : ℚ) := by
      push_cast
      apply mul_left_cancel₀ hqe
      linear_combination h6
    exact_mod_cast key
  · have hD3 : (d₂ : ℚ) * (q + 1) - 1 ≠ 0 := by
      have : (d₂ * (q + 1) - 1 : ℤ) ≠ 0 := by nlinarith
      exact_mod_cast this
    have hqe : (q : ℚ) + 1 ≠ 0 := by
      have : (q : ℤ) + 1 ≠ 0 := by omega
      exact_mod_cast this
    push_cast at h6
    rw [show ((q : ℚ) - -1) * d₂ + -1 = d₂ * (q + 1) - 1 by ring] at h6
    field_simp at h6
    have key : ((q * a * (d₂ - 1) ^ 2 : ℤ) : ℚ) =
        (((q + -1) ^ 2 * d₂ * ((q - -1) * d₂ + -1) : ℤ) : ℚ) := by
      push_cast
      apply mul_left_cancel₀ hqe
      linear_combination h6
    exact_mod_cast key

theorem prime_pow_dvd_mul_of_coprime {p : ℕ} (hp : p.Prime) {m : ℕ} {x y : ℤ}
    (hxy : IsCoprime x y) (h : ((p : ℤ) ^ m) ∣ x * y) :
    ((p : ℤ) ^ m) ∣ x ∨ ((p : ℤ) ^ m) ∣ y := by
  have hpi : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  by_cases hpx : (p : ℤ) ∣ x
  · left
    have hpy : ¬ (p : ℤ) ∣ y := by
      intro hpy
      exact hpi.not_isUnit (hxy.isUnit_of_dvd' hpx hpy)
    have hc : IsCoprime ((p : ℤ) ^ m) y :=
      ((Irreducible.coprime_iff_not_dvd hpi.irreducible).mpr hpy).pow_left
    exact hc.dvd_of_dvd_mul_right h
  · right
    have hc : IsCoprime ((p : ℤ) ^ m) x :=
      ((Irreducible.coprime_iff_not_dvd hpi.irreducible).mpr hpx).pow_left
    exact hc.dvd_of_dvd_mul_left h

theorem eight_numth {p m : ℕ} (hp : p.Prime) {q e a d₂ : ℤ} (hqpm : q = (p : ℤ) ^ m)
    (hq : 27 ≤ q) (he : IsSign e) (hq8 : q % 8 = 4 + e) (pd₂ : 0 < d₂)
    (hstar : q * a * (d₂ - 1) ^ 2 = (q + e) ^ 2 * d₂ * ((q - e) * d₂ + e))
    {R : ℤ} (hR : 2 * R = q + e) (hRo : R ∣ d₂ - 1) (hpar : Odd d₂) (hsyl : (8 : ℤ) ∣ d₂ - 7)
    (hint : ((q - e) * d₂ + e) ∣ q ^ 3 * a) :
    d₂ = q * (q + e) + 1 ∧ a = q * (q + e) + 1 := by
  have hee := he.sq
  have hqe : 0 < q + e := by rcases he with rfl | rfl <;> omega
  have pd₃ : 0 < (q - e) * d₂ + e := by rcases he with rfl | rfl <;> nlinarith
  have hRodd : Odd R := by
    rcases he with rfl | rfl
    · exact ⟨(R - 1) / 2, by omega⟩
    · exact ⟨(R - 1) / 2, by omega⟩
  obtain ⟨t, ht⟩ := hRo
  have htev : Even t := by
    have hev : Even (d₂ - 1) := by
      obtain ⟨k, hk⟩ := hpar
      exact ⟨k, by omega⟩
    rw [ht] at hev
    rcases Int.even_or_odd t with h | h
    · exact h
    · exact absurd hev (Int.not_even_iff_odd.mpr (Int.odd_mul.mpr ⟨hRodd, h⟩))
  obtain ⟨b, hb⟩ := htev
  have hbq : d₂ - 1 = b * (q + e) := by rw [ht, hb]; linear_combination b * hR
  have hb0 : 0 < b := by
    have h1 : 0 ≤ b * (q + e) := by rw [← hbq]; omega
    have h2 : 0 ≤ b := by
      by_contra h
      push Not at h
      nlinarith
    rcases h2.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, zero_mul] at hbq
      have hd2 : d₂ = 1 := by omega
      rw [hd2] at hstar pd₃
      simp at hstar
      rcases hstar with h' | h' <;> omega
  obtain ⟨c, hc⟩ := hint
  have hd30 : ((q - e) * d₂ + e) ≠ 0 := pd₃.ne'
  have hc2 : c * (d₂ - 1) ^ 2 = q ^ 2 * (q + e) ^ 2 * d₂ := by
    apply mul_left_cancel₀ hd30
    linear_combination q ^ 2 * hstar - (d₂ - 1) ^ 2 * hc
  have hdiv : (d₂ - 1) ^ 2 ∣ (q * (q + e)) ^ 2 * d₂ := ⟨c, by linear_combination -hc2⟩
  have hcop : IsCoprime ((d₂ - 1) ^ 2) d₂ := (IsCoprime.pow_left ⟨-1, 1, by ring⟩)
  have hdiv3 : d₂ - 1 ∣ q * (q + e) :=
    (Int.pow_dvd_pow_iff two_ne_zero).mp (hcop.dvd_of_dvd_mul_right hdiv)
  rw [hbq] at hdiv3
  have hbdvd : b ∣ q := (mul_dvd_mul_iff_right hqe.ne').mp hdiv3
  have hqd : q ∣ d₂ * ((q - e) * d₂ + e) := by
    have h1 : q ∣ (q + e) ^ 2 * (d₂ * ((q - e) * d₂ + e)) :=
      ⟨a * (d₂ - 1) ^ 2, by linear_combination -hstar⟩
    have hc1 : IsCoprime q ((q + e) ^ 2) := IsCoprime.pow_right ⟨-e, e, by linear_combination hee⟩
    exact hc1.dvd_of_dvd_mul_left h1
  have hcop23 : IsCoprime d₂ ((q - e) * d₂ + e) :=
    ⟨-e * (q - e), e, by linear_combination hee⟩
  have hsplit := prime_pow_dvd_mul_of_coprime (m := m) hp hcop23 (by rw [← hqpm]; exact hqd)
  rw [← hqpm] at hsplit
  rcases hsplit with h | h
  ·
    exfalso
    have hbe : q ∣ b * e + 1 := by
      have : d₂ = q * b + (b * e + 1) := by linear_combination hbq
      rw [this] at h
      exact (dvd_add_right (dvd_mul_right q b)).mp h
    have hbleq : b ≤ q := Int.le_of_dvd (by omega) hbdvd
    obtain ⟨s, hs⟩ := hbe
    rcases he with rfl | rfl
    ·
      have hs1 : s = 1 := by
        have h1 : 0 < q * s := by omega
        have h2 : q * s ≤ q + 1 := by omega
        have h3 : 0 < s := by
          by_contra h'
          push Not at h'
          nlinarith
        have h4 : s < 2 := by
          by_contra h'
          push Not at h'
          nlinarith
        omega
      rw [hs1] at hs
      have hb1 : b = q - 1 := by linarith
      have : q - 1 ∣ 1 := by
        have h1 : q - 1 ∣ q := hb1 ▸ hbdvd
        have := dvd_sub h1 (dvd_refl (q - 1))
        simpa using this
      have := Int.le_of_dvd one_pos this
      omega
    ·
      have hs0 : s = 0 := by
        have h1 : q * s ≤ 0 := by linarith
        have h2 : -q < q * s := by linarith
        have h3 : s ≤ 0 := by
          by_contra h'
          push Not at h'
          nlinarith
        have h4 : -1 < s := by
          by_contra h'
          push Not at h'
          nlinarith
        omega
      rw [hs0] at hs
      have hb1 : b = 1 := by linarith
      rw [hb1] at hbq
      have hd2 : d₂ = q := by linarith
      rw [hd2] at hsyl
      omega
  ·
    have hqb : q ∣ b := by
      have h3 : (q - e) * d₂ + e = q * (b * q + 1) - b := by
        have : d₂ = b * (q + e) + 1 := by linarith
        rw [this]
        linear_combination (-b) * hee
      rw [h3] at h
      exact (dvd_sub_right (dvd_mul_right q (b * q + 1))).mp h
    have hbq' : b = q := Int.dvd_antisymm hb0.le (by omega) hbdvd hqb
    rw [hbq'] at hbq
    have hd2 : d₂ = q * (q + e) + 1 := by linarith
    refine ⟨hd2, ?_⟩
    rw [hd2] at hstar
    have hq3 : q ^ 3 * (q + e) ^ 2 ≠ 0 := by positivity
    apply mul_left_cancel₀ hq3
    linear_combination hstar - (q + e) ^ 2 * (q * (q + e) + 1) * q * hee

theorem eight_quad {q e f₅ f₆ : ℤ} (hq : 27 ≤ q) (he : IsSign e) (hf₅ : f₅ ≠ 0) (hf₆ : f₆ ≠ 0)
    (h20 : (((q ^ 3 * (q ^ 2 - 1) * (q * (q + e) + 1)) : ℤ) : ℚ) *
      ((q : ℚ) ^ 2 * (-e : ℤ) / ((q ^ 3 : ℤ) : ℚ) +
        (q : ℚ) ^ 2 * (e : ℤ) / ((q * (q * (q + e) + 1) : ℤ) : ℚ) +
        ((q : ℚ) + e) ^ 2 / (4 * f₅) + ((q : ℚ) + e) ^ 2 / (4 * f₆)) =
      -e * q ^ 2 * (q ^ 2 - 1) * (q + e) * (3 * q + e))
    (hdeg : (-e) * q ^ 3 + e * (q * (q * (q + e) + 1)) + f₅ + f₆ = 0) :
    e = -1 ∧ ∃ s : ℤ, s ^ 2 = 3 * q := by
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hq1 : (q : ℚ) ^ 2 - 1 ≠ 0 := by
    have : (q : ℤ) ^ 2 - 1 ≠ 0 := by nlinarith
    exact_mod_cast this
  have hf5 : (f₅ : ℚ) ≠ 0 := by exact_mod_cast hf₅
  have hf6 : (f₆ : ℚ) ≠ 0 := by exact_mod_cast hf₆
  rcases he with rfl | rfl
  · exfalso
    have hd2 : (q : ℚ) * (q + 1) + 1 ≠ 0 := by
      have : (q * (q + 1) + 1 : ℤ) ≠ 0 := by nlinarith
      exact_mod_cast this
    have hqp : (q : ℚ) + 1 ≠ 0 := by
      have : (q + 1 : ℤ) ≠ 0 := by omega
      exact_mod_cast this
    push_cast at h20
    have hA : ((q : ℚ) ^ 3 * (q ^ 2 - 1) * (q * (q + 1) + 1)) *
        ((q : ℚ) ^ 2 * (-1) / q ^ 3 + (q : ℚ) ^ 2 * 1 / (q * (q * (q + 1) + 1))) =
        -q ^ 2 * (q ^ 2 - 1) * (q + 1) := by
      field_simp
      ring
    have hB : ((q : ℚ) ^ 3 * (q ^ 2 - 1) * (q * (q + 1) + 1)) *
        (((q : ℚ) + 1) ^ 2 / (4 * f₅) + ((q : ℚ) + 1) ^ 2 / (4 * f₆)) =
        -3 * q ^ 3 * (q ^ 2 - 1) * (q + 1) := by
      linear_combination h20 - hA
    have hf : (f₆ : ℚ) = -q * (q + 1) - f₅ := by
      have : f₆ = -q * (q + 1) - f₅ := by linear_combination hdeg
      exact_mod_cast this
    have hD : (q : ℚ) * (q * (q + 1) + 1) * (q + 1) ^ 2 = 12 * f₅ * f₆ := by
      field_simp at hB
      rw [hf] at hB ⊢
      linear_combination -hB
    have hF : ((12 * f₅ + 6 * q * (q + 1) : ℤ) : ℚ) ^ 2 = -12 * q * (q + 1) ^ 2 * (q - 1) ^ 2 := by
      push_cast
      rw [hf] at hD
      linear_combination 12 * hD
    have h1 : (0 : ℚ) ≤ ((12 * f₅ + 6 * q * (q + 1) : ℤ) : ℚ) ^ 2 := sq_nonneg _
    have h2 : -12 * (q : ℚ) * (q + 1) ^ 2 * (q - 1) ^ 2 < 0 := by
      have : (0 : ℚ) < q := by exact_mod_cast (show (0 : ℤ) < q by omega)
      have h3 : (0 : ℚ) < (q + 1) ^ 2 * (q - 1) ^ 2 := by
        have : (0 : ℚ) < (q - 1) := by
          have : ((1 : ℤ) : ℚ) < q := by exact_mod_cast (show (1 : ℤ) < q by omega)
          push_cast at this; linarith
        positivity
      nlinarith
    linarith
  · refine ⟨rfl, ?_⟩
    have hd2 : (q : ℚ) * (q + -1) + 1 ≠ 0 := by
      have : (q * (q + -1) + 1 : ℤ) ≠ 0 := by nlinarith
      exact_mod_cast this
    have hqm : (q : ℚ) + -1 ≠ 0 := by
      have : (q + -1 : ℤ) ≠ 0 := by omega
      exact_mod_cast this
    push_cast at h20
    have hA : ((q : ℚ) ^ 3 * (q ^ 2 - 1) * (q * (q + -1) + 1)) *
        ((q : ℚ) ^ 2 * (-(-1)) / q ^ 3 + (q : ℚ) ^ 2 * (-1) / (q * (q * (q + -1) + 1))) =
        -q ^ 2 * (q ^ 2 - 1) * (q + -1) := by
      field_simp
      ring
    have hB : ((q : ℚ) ^ 3 * (q ^ 2 - 1) * (q * (q + -1) + 1)) *
        (((q : ℚ) + -1) ^ 2 / (4 * f₅) + ((q : ℚ) + -1) ^ 2 / (4 * f₆)) =
        3 * q ^ 3 * (q ^ 2 - 1) * (q + -1) := by
      linear_combination h20 - hA
    have hf : (f₆ : ℚ) = -q * (q + -1) - f₅ := by
      have : f₆ = -q * (q + -1) - f₅ := by linear_combination hdeg
      exact_mod_cast this
    have hD : -(q : ℚ) * (q * (q + -1) + 1) * (q + -1) ^ 2 = 12 * f₅ * f₆ := by
      field_simp at hB
      rw [hf] at hB ⊢
      linear_combination hB
    have hF : ((12 * f₅ + 6 * q * (q - 1) : ℤ) : ℚ) ^ 2 =
        3 * q * ((2 * (q ^ 2 - 1) : ℤ) : ℚ) ^ 2 := by
      push_cast
      rw [hf] at hD
      linear_combination 12 * hD
    have hZ : (12 * f₅ + 6 * q * (q - 1)) ^ 2 = 3 * q * (2 * (q ^ 2 - 1)) ^ 2 := by
      exact_mod_cast hF
    have hW : (2 * (q ^ 2 - 1) : ℤ) ≠ 0 := by nlinarith
    have hdvd : (2 * (q ^ 2 - 1)) ∣ (12 * f₅ + 6 * q * (q - 1)) :=
      (Int.pow_dvd_pow_iff two_ne_zero).mp ⟨3 * q, by rw [hZ]; ring⟩
    obtain ⟨s, hs⟩ := hdvd
    refine ⟨s, ?_⟩
    rw [hs] at hZ
    have : (2 * (q ^ 2 - 1)) ^ 2 * s ^ 2 = (2 * (q ^ 2 - 1)) ^ 2 * (3 * q) := by
      linear_combination hZ
    exact mul_left_cancel₀ (pow_ne_zero 2 hW) this

theorem three_q_sq {p m : ℕ} (hp : p.Prime) {q s : ℤ} (hqpm : q = (p : ℤ) ^ m) (hq : 27 ≤ q)
    (hs : s ^ 2 = 3 * q) : ∃ k : ℕ, 1 ≤ k ∧ q = 3 ^ (2 * k + 1) := by
  have h3 : Prime (3 : ℤ) := Int.prime_three
  have h3s : (3 : ℤ) ∣ s := h3.dvd_of_dvd_pow (n := 2) ⟨q, by rw [hs]⟩
  obtain ⟨t, rfl⟩ := h3s
  have hq3 : q = 3 * t ^ 2 := by
    have h9 : 3 * q = 3 * (3 * t ^ 2) := by linear_combination -hs
    linarith
  have h3q : (3 : ℤ) ∣ (p : ℤ) ^ m := by rw [← hqpm, hq3]; exact dvd_mul_right _ _
  have hp3 : p = 3 := by
    have h1 : (3 : ℤ) ∣ (p : ℤ) := h3.dvd_of_dvd_pow h3q
    have h2 : (3 : ℕ) ∣ p := by exact_mod_cast h1
    exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h2).symm
  subst hp3
  have hn : ((3 * t).natAbs) ^ 2 = 3 ^ (m + 1) := by
    have h1 : ((3 * t) ^ 2 : ℤ) = 3 ^ (m + 1) := by rw [hs, hqpm]; push_cast; ring
    have h2 : (((3 * t).natAbs ^ 2 : ℕ) : ℤ) = ((3 ^ (m + 1) : ℕ) : ℤ) := by
      push_cast
      rw [sq_abs]
      exact h1
    exact_mod_cast h2
  have hdvd : (3 * t).natAbs ∣ 3 ^ (m + 1) := ⟨(3 * t).natAbs, by rw [← hn]; ring⟩
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  rw [hj, ← pow_mul] at hn
  have hjm : j * 2 = m + 1 := Nat.pow_right_injective (le_refl 2) (by simpa using hn)
  have hm : 3 ≤ m := by
    by_contra h
    push Not at h
    have : q ≤ 9 := by
      rw [hqpm]
      have : (3 : ℤ) ^ m ≤ 3 ^ 2 := pow_le_pow_right₀ (by norm_num) (by omega)
      push_cast
      linarith
    omega
  refine ⟨j - 1 - 1 + 1, by omega, ?_⟩
  rw [hqpm]
  push_cast
  congr 1
  omega

theorem eight_arith' {p m : ℕ} (hp : p.Prime) {q e a d₂ d₃ d₄ δ₂ δ₃ δ₄ e₂ e₃ e₄ D f₅ f₆ R : ℤ}
    (hqpm : q = (p : ℤ) ^ m) (hq : 27 ≤ q) (he : IsSign e) (hq8 : q % 8 = 4 + e) (ha : 0 < a)
    (h₂ : IsSign δ₂) (h₃ : IsSign δ₃) (h₄ : IsSign δ₄)
    (pd₂ : 0 < d₂) (pd₃ : 0 < d₃) (pd₄ : 0 < d₄) (hD : D ≠ 0) (hf₅ : f₅ ≠ 0) (hf₆ : f₆ ≠ 0)
    (h6 : ((q ^ 3 * (q ^ 2 - 1) * a : ℤ) : ℚ) *
      (1 + δ₂ / d₂ + δ₃ * q ^ 2 / d₃ + δ₄ * q ^ 2 / d₄) = q ^ 2 * (q ^ 2 - 1) ^ 2 * (q + e))
    (h8 : ((q : ℚ) + e) * (q * (q ^ 2 - 1)) ^ 2 = ((q ^ 3 * (q ^ 2 - 1) * a : ℤ) : ℚ) *
      (2 * (q - e) ^ 2 * e / D + 1 + e₂ / d₂ + e₃ * q ^ 2 / d₃ + e₄ * q ^ 2 / d₄))
    (R1 : 1 + δ₂ * e₂ + δ₃ * e₃ + δ₄ * e₄ = 0)
    (R2 : 2 * e * D + 1 + e₂ * d₂ + e₃ * d₃ + e₄ * d₄ = 0)
    (R3 : 1 + δ₂ * d₂ + δ₃ * d₃ + δ₄ * d₄ = 0)
    (O2 : δ₃ * e₃ + δ₄ * e₄ = 0) (FS : 1 + δ₂ + δ₃ + δ₄ = 0)
    (hR : 2 * R = q + e) (hRo : R ∣ d₂ - e₂) (hpar : ∃ k, d₂ = δ₂ + 2 * k)
    (hsyl : (8 : ℤ) ∣ d₂ + 7 * δ₂) (hint₃ : d₃ ∣ q ^ 2 * a * (-e * q * δ₃))
    (h20 : ((q ^ 3 * (q ^ 2 - 1) * a : ℤ) : ℚ) *
      ((q : ℚ) ^ 2 * δ₃ / d₃ + (q : ℚ) ^ 2 * δ₄ / d₄ +
        ((q : ℚ) + e) ^ 2 / (4 * f₅) + ((q : ℚ) + e) ^ 2 / (4 * f₆)) =
      -e * q ^ 2 * (q ^ 2 - 1) * (q + e) * (3 * q + e))
    (hdeg : δ₃ * d₃ + δ₄ * d₄ + f₅ + f₆ = 0) (hσ : δ₃ = e₃) :
    e = -1 ∧ (∃ k : ℕ, 1 ≤ k ∧ q = 3 ^ (2 * k + 1)) ∧
      q ^ 3 * (q ^ 2 - 1) * a = q ^ 3 * (q ^ 3 + 1) * (q - 1) := by
  have hg : q ^ 3 * (q ^ 2 - 1) * a ≠ 0 := by
    have : 0 < q ^ 2 - 1 := by nlinarith
    positivity
  obtain ⟨he₂, he₄, hδ₃, hδ₄, hd₄, hd₃⟩ := eight_signs hq he h₂ h₃ h₄ pd₂ pd₃ pd₄ hD hg h6 h8 R1
    R2 R3 O2 hσ
  have hee := he.sq
  have hδ₂ : δ₂ = -1 := by
    rw [hδ₃, hδ₄] at FS
    linarith
  rw [hδ₂] at hδ₃ hδ₄ he₂ hd₃
  have hδ₃' : δ₃ = -e := by rw [hδ₃]; ring
  have hδ₄' : δ₄ = e := by rw [hδ₄]; ring
  have hd₃' : d₃ = (q - e) * d₂ + e := by rw [hd₃]; ring
  have he₂' : e₂ = 1 := by rw [he₂]; ring
  have hstar := eight_ten (a := a) hq he pd₂ (by rw [← hd₃']; exact pd₃) (by
    rw [← hd₃']
    rw [hδ₂, hδ₃', hδ₄', hd₄] at h6
    push_cast at h6 ⊢
    exact h6)
  have hpar' : Odd d₂ := by
    obtain ⟨k, hk⟩ := hpar
    rw [hδ₂] at hk
    exact ⟨k - 1, by omega⟩
  have hint' : ((q - e) * d₂ + e) ∣ q ^ 3 * a := by
    rw [← hd₃']
    rw [hδ₃'] at hint₃
    have : q ^ 2 * a * (-e * q * -e) = q ^ 3 * a := by linear_combination q ^ 3 * a * hee
    rwa [this] at hint₃
  obtain ⟨hd₂', ha'⟩ := eight_numth hp hqpm hq he hq8 pd₂ hstar hR (by rw [he₂'] at hRo; exact hRo)
    hpar' (by rw [hδ₂, show d₂ + 7 * -1 = d₂ - 7 by ring] at hsyl; exact hsyl) hint'
  have hd₃q : d₃ = q ^ 3 := by rw [hd₃', hd₂']; linear_combination (-q) * hee
  obtain ⟨he1, s, hs⟩ := eight_quad (f₅ := f₅) (f₆ := f₆) hq he hf₅ hf₆ (by
    rw [ha', hδ₃', hδ₄', hd₄, hd₂', hd₃q] at h20
    push_cast at h20 ⊢
    exact h20) (by rw [hδ₃', hδ₄', hd₃q, hd₄, hd₂'] at hdeg; exact hdeg)
  obtain ⟨k, hk, hqk⟩ := three_q_sq hp hqpm hq hs
  refine ⟨he1, ⟨k, hk, hqk⟩, ?_⟩
  rw [ha', he1]
  ring

theorem eight_arith {p m : ℕ} (hp : p.Prime) {q e a d₂ d₃ d₄ δ₂ δ₃ δ₄ e₂ e₃ e₄ D f₅ f₆ R : ℤ}
    (hqpm : q = (p : ℤ) ^ m) (hq : 27 ≤ q) (he : IsSign e) (hq8 : q % 8 = 4 + e) (ha : 0 < a)
    (h₂ : IsSign δ₂) (h₃ : IsSign δ₃) (h₄ : IsSign δ₄) (k₃ : IsSign e₃)
    (pd₂ : 0 < d₂) (pd₃ : 0 < d₃) (pd₄ : 0 < d₄) (hD : D ≠ 0) (hf₅ : f₅ ≠ 0) (hf₆ : f₆ ≠ 0)
    (h6 : ((q ^ 3 * (q ^ 2 - 1) * a : ℤ) : ℚ) *
      (1 + δ₂ / d₂ + δ₃ * q ^ 2 / d₃ + δ₄ * q ^ 2 / d₄) = q ^ 2 * (q ^ 2 - 1) ^ 2 * (q + e))
    (h8 : ((q : ℚ) + e) * (q * (q ^ 2 - 1)) ^ 2 = ((q ^ 3 * (q ^ 2 - 1) * a : ℤ) : ℚ) *
      (2 * (q - e) ^ 2 * e / D + 1 + e₂ / d₂ + e₃ * q ^ 2 / d₃ + e₄ * q ^ 2 / d₄))
    (R1 : 1 + δ₂ * e₂ + δ₃ * e₃ + δ₄ * e₄ = 0)
    (R2 : 2 * e * D + 1 + e₂ * d₂ + e₃ * d₃ + e₄ * d₄ = 0)
    (R3 : 1 + δ₂ * d₂ + δ₃ * d₃ + δ₄ * d₄ = 0)
    (O2 : δ₃ * e₃ + δ₄ * e₄ = 0) (FS : 1 + δ₂ + δ₃ + δ₄ = 0)
    (hR : 2 * R = q + e) (hRo : R ∣ d₂ - e₂) (hpar : ∃ k, d₂ = δ₂ + 2 * k)
    (hsyl : (8 : ℤ) ∣ d₂ + 7 * δ₂) (hint₃ : d₃ ∣ q ^ 2 * a * (-e * q * δ₃))
    (hint₄ : d₄ ∣ q ^ 2 * a * (-e * q * δ₄))
    (h20 : ((q ^ 3 * (q ^ 2 - 1) * a : ℤ) : ℚ) *
      ((q : ℚ) ^ 2 * δ₃ / d₃ + (q : ℚ) ^ 2 * δ₄ / d₄ +
        ((q : ℚ) + e) ^ 2 / (4 * f₅) + ((q : ℚ) + e) ^ 2 / (4 * f₆)) =
      -e * q ^ 2 * (q ^ 2 - 1) * (q + e) * (3 * q + e))
    (hdeg : δ₃ * d₃ + δ₄ * d₄ + f₅ + f₆ = 0) :
    e = -1 ∧ (∃ k : ℕ, 1 ≤ k ∧ q = 3 ^ (2 * k + 1)) ∧
      q ^ 3 * (q ^ 2 - 1) * a = q ^ 3 * (q ^ 3 + 1) * (q - 1) := by
  have h33 := h₃.sq
  rcases (h₃.mul k₃) with hσ | hσ
  · have hσ' : δ₃ = e₃ := by linear_combination (-δ₃) * hσ + e₃ * h33
    exact eight_arith' hp hqpm hq he hq8 ha h₂ h₃ h₄ pd₂ pd₃ pd₄ hD hf₅ hf₆ h6 h8 R1 R2 R3 O2 FS
      hR hRo hpar hsyl hint₃ h20 hdeg hσ'
  ·
    have h44 := h₄.sq
    have hσ4 : δ₄ * e₄ = 1 := by linarith
    have hσ' : δ₄ = e₄ := by linear_combination (-δ₄) * hσ4 + e₄ * h44
    exact eight_arith' (d₃ := d₄) (d₄ := d₃) (δ₃ := δ₄) (δ₄ := δ₃) (e₃ := e₄) (e₄ := e₃)
      hp hqpm hq he hq8 ha h₂ h₄ h₃ pd₂ pd₄ pd₃ hD hf₅ hf₆
      (by linear_combination h6) (by linear_combination h8) (by linear_combination R1)
      (by linear_combination R2) (by linear_combination R3) (by linear_combination O2)
      (by linear_combination FS) hR hRo hpar hsyl hint₄ (by linear_combination h20)
      (by linear_combination hdeg) hσ'

end CFSG.Walter.Ward
