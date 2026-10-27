module

public import CFSG.RankThree.PartOne.KC.EvenSymplecticFourRootAxisGood
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.RankThree.PartTwo.Sec18

open Matrix
open CFSG.RankThree.PartOne.KCRootAxis (SL₂)

theorem det_sl2_189 {F : Type} [Field F] (x : SL₂ F) : x 0 0 * x 1 1 - x 0 1 * x 1 0 = 1 := by
  have := x.property
  rwa [Matrix.det_fin_two] at this

theorem add_eq_one_of_pow_three_sl2189 {F : Type} [Field F] [CharP F 2] {x : SL₂ F}
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) : x 0 0 + x 1 1 = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hdet := det_sl2_189 x
  have h3 : (x : Matrix (Fin 2) (Fin 2) F) * x * x = 1 := by
    rw [← pow_three']
    exact congrArg Subtype.val hx3
  have e00 := congrFun (congrFun h3 0) 0
  have e01 := congrFun (congrFun h3 0) 1
  have e10 := congrFun (congrFun h3 1) 0
  have e11 := congrFun (congrFun h3 1) 1
  simp only [mul_apply, Fin.sum_univ_two, Fin.isValue, one_apply_eq, ne_eq, zero_ne_one,
    one_ne_zero, not_false_eq_true, one_apply_ne] at e00 e01 e10 e11
  by_contra hne
  have hs : x 0 0 + x 1 1 + 1 ≠ 0 := fun hs => hne (by linear_combination hs - h2)
  have hs2 : (x 0 0 + x 1 1 + 1) ^ 2 ≠ 0 := pow_ne_zero 2 hs
  have hb : x 0 1 = 0 := (mul_eq_zero.mp (by
    linear_combination e01 + x 0 1 * hdet + x 0 1 * (x 0 0 + x 1 1 + 1) * h2 :
    x 0 1 * (x 0 0 + x 1 1 + 1) ^ 2 = 0)).resolve_right hs2
  have hc : x 1 0 = 0 := (mul_eq_zero.mp (by
    linear_combination e10 + x 1 0 * hdet + x 1 0 * (x 0 0 + x 1 1 + 1) * h2 :
    x 1 0 * (x 0 0 + x 1 1 + 1) ^ 2 = 0)).resolve_right hs2
  have ha : x 0 0 * (x 0 0 + x 1 1 + 1) = 1 := mul_right_cancel₀ hs (by
    linear_combination e00 + (2 * x 0 0 + x 1 1) * hdet + x 0 0 * (x 0 0 + x 1 1 + 1) * h2)
  have hd : x 1 1 * (x 0 0 + x 1 1 + 1) = 1 := mul_right_cancel₀ hs (by
    linear_combination e11 + (2 * x 1 1 + x 0 0) * hdet + x 1 1 * (x 0 0 + x 1 1 + 1) * h2)
  have had : x 0 0 = x 1 1 := mul_right_cancel₀ hs (ha.trans hd.symm)
  have hs1 : x 0 0 + x 1 1 + 1 = 1 := by linear_combination x 0 0 * h2 - had
  rw [hs1, mul_one] at ha hd
  apply hx1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd]

theorem exists_mul_self_of_matrix189 {F : Type} [Field F] {x : SL₂ F}
    (t : Matrix (Fin 2) (Fin 2) F) (ht : t.det = 1) (htt : t * t = 1)
    (htx : t * x * t = adjugate (x : Matrix (Fin 2) (Fin 2) F)) :
    ∃ w : SL₂ F, w * w = 1 ∧ w * x * w = x⁻¹ :=
  ⟨⟨t, ht⟩, Subtype.ext htt, Subtype.ext htx⟩

theorem exists_involution_inv_sl2_189 {F : Type} [Field F] [CharP F 2] {x : SL₂ F}
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) : ∃ w : SL₂ F, w * w = 1 ∧ w * x * w⁻¹ = x⁻¹ := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have htr := add_eq_one_of_pow_three_sl2189 hx3 hx1
  suffices h : ∃ w : SL₂ F, w * w = 1 ∧ w * x * w = x⁻¹ by
    obtain ⟨w, hw, hwx⟩ := h
    exact ⟨w, hw, by rw [inv_eq_of_mul_eq_one_right hw, hwx]⟩
  by_cases hb : x 0 1 = 0
  · by_cases hc : x 1 0 = 0
    · refine exists_mul_self_of_matrix189 !![0, 1; 1, 0]
        (by rw [det_fin_two_of]; linear_combination -h2) ?_ ?_
      · ext i j
        fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two]
      · ext i j
        fin_cases i <;> fin_cases j <;>
          simp [mul_apply, vecMul, dotProduct, Fin.sum_univ_two, adjugate_fin_two, hb, hc]
    · obtain ⟨t, ht⟩ : ∃ t : F, x 1 0 * t = 1 := ⟨(x 1 0)⁻¹, mul_inv_cancel₀ hc⟩
      refine exists_mul_self_of_matrix189 !![1, t; 0, 1] (by simp [det_fin_two_of]) ?_ ?_
      · ext i j
        fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two]
        linear_combination t * h2
      · ext i j
        fin_cases i <;> fin_cases j <;>
          simp [mul_apply, vecMul, dotProduct, Fin.sum_univ_two, adjugate_fin_two]
        · linear_combination ht + htr + (1 - x 1 1) * h2
        · linear_combination t * ht + t * htr + (t + x 0 1) * h2
        · linear_combination x 1 0 * h2
        · linear_combination ht + htr + (1 - x 0 0) * h2
  · obtain ⟨t, ht⟩ : ∃ t : F, x 0 1 * t = 1 := ⟨(x 0 1)⁻¹, mul_inv_cancel₀ hb⟩
    refine exists_mul_self_of_matrix189 !![1, 0; t, 1] (by simp [det_fin_two_of]) ?_ ?_
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two]
      linear_combination t * h2
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [mul_apply, vecMul, dotProduct, Fin.sum_univ_two, adjugate_fin_two]
      · linear_combination ht + htr + (1 - x 1 1) * h2
      · linear_combination x 0 1 * h2
      · linear_combination t * ht + t * htr + (t + x 1 0) * h2
      · linear_combination ht + htr + (1 - x 0 0) * h2

theorem pow_smul_add_smul189 {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    {e₁ e₂ : A} (h11 : e₁ * e₁ = e₁) (h12 : e₁ * e₂ = 0) (h21 : e₂ * e₁ = 0) (h22 : e₂ * e₂ = e₂)
    (hsum : e₁ + e₂ = 1) (a b : R) (n : ℕ) : (a • e₁ + b • e₂) ^ n = a ^ n • e₁ + b ^ n • e₂ := by
  induction n with
  | zero => simp [hsum]
  | succ n ih =>
    rw [pow_succ, ih]
    simp only [add_mul, mul_add, smul_mul_smul_comm, h11, h12, h21, h22, smul_zero, add_zero,
      zero_add, pow_succ]

theorem exists_orderOf_five_commute_sl2189 {F : Type} [Field F] [CharP F 2] {ω μ : F}
    (hω : ω ^ 2 + ω + 1 = 0) (hμ5 : μ ^ 5 = 1) (hμ1 : μ ≠ 1) {x : SL₂ F}
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) : ∃ y : SL₂ F, y * x = x * y ∧ orderOf y = 5 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have htr := add_eq_one_of_pow_three_sl2189 hx3 hx1
  have hdet := det_sl2_189 x
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  obtain ⟨E₁, hE₁⟩ : ∃ E : Matrix (Fin 2) (Fin 2) F,
      E = (x : Matrix (Fin 2) (Fin 2) F) + ω ^ 2 • 1 := ⟨_, rfl⟩
  obtain ⟨E₂, hE₂⟩ : ∃ E : Matrix (Fin 2) (Fin 2) F,
      E = (x : Matrix (Fin 2) (Fin 2) F) + ω • 1 := ⟨_, rfl⟩
  have h12 : E₁ * E₂ = 0 := by
    rw [hE₁, hE₂]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two]
    · linear_combination x 0 0 * hω + hω3 + x 0 0 * htr - hdet
    · linear_combination x 0 1 * hω + x 0 1 * htr
    · linear_combination x 1 0 * hω + x 1 0 * htr
    · linear_combination x 1 1 * hω + hω3 + x 1 1 * htr - hdet
  have h21 : E₂ * E₁ = 0 := by
    rw [hE₁, hE₂]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two]
    · linear_combination x 0 0 * hω + hω3 + x 0 0 * htr - hdet
    · linear_combination x 0 1 * hω + x 0 1 * htr
    · linear_combination x 1 0 * hω + x 1 0 * htr
    · linear_combination x 1 1 * hω + hω3 + x 1 1 * htr - hdet
  have hsum : E₁ + E₂ = 1 := by
    rw [hE₁, hE₂]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    · linear_combination (x 0 0 - 1) * h2 + hω
    · linear_combination x 0 1 * h2
    · linear_combination x 1 0 * h2
    · linear_combination (x 1 1 - 1) * h2 + hω
  have h11 : E₁ * E₁ = E₁ := by
    have := congrArg (E₁ * ·) hsum
    simpa [mul_add, h12] using this
  have h22 : E₂ * E₂ = E₂ := by
    have := congrArg (E₂ * ·) hsum
    simpa [mul_add, h21] using this
  have hdetY : (μ • E₁ + μ ^ 4 • E₂).det = 1 := by
    rw [det_fin_two, hE₁, hE₂]
    simp
    linear_combination (μ + μ ^ 4) ^ 2 * hdet + (μ * ω ^ 2 + μ ^ 4 * ω) * (μ + μ ^ 4) * htr +
      (μ ^ 2 * (ω ^ 2 - ω + 1) + μ ^ 8 + μ ^ 5) * hω + hμ5 + μ ^ 5 * ω ^ 3 * h2
  have hY5 : (μ • E₁ + μ ^ 4 • E₂) ^ 5 = 1 := by
    have h20 : (μ ^ 4) ^ 5 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hμ5, one_pow]
    rw [pow_smul_add_smul189 h11 h12 h21 h22 hsum, hμ5, h20, one_smul, one_smul, hsum]
  have hY1 : μ • E₁ + μ ^ 4 • E₂ ≠ 1 := by
    intro hY
    have h1 : μ • E₁ = E₁ := by
      have := congrArg (· * E₁) hY
      simpa [add_mul, smul_mul_assoc, h11, h21] using this
    have htrE : E₁.trace = 1 := by
      rw [hE₁, trace_fin_two]
      simp
      linear_combination htr + ω ^ 2 * h2
    have := congrArg Matrix.trace h1
    rw [trace_smul, htrE, smul_eq_mul, mul_one] at this
    exact hμ1 this
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine ⟨⟨μ • E₁ + μ ^ 4 • E₂, hdetY⟩, ?_, orderOf_eq_prime (Subtype.ext ?_) ?_⟩
  · apply Subtype.ext
    change (μ • E₁ + μ ^ 4 • E₂) * (x : Matrix (Fin 2) (Fin 2) F) =
      (x : Matrix (Fin 2) (Fin 2) F) * (μ • E₁ + μ ^ 4 • E₂)
    rw [hE₁, hE₂]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  · exact hY5
  · intro h
    exact hY1 (congrArg Subtype.val h)

theorem exists_orderOf_five_commute_sl2_sixteen189 {x : SL₂ (GaloisField 2 4)}
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    ∃ y : SL₂ (GaloisField 2 4), y * x = x * y ∧ orderOf y = 5 := by
  have hcard : Nat.card (GaloisField 2 4)ˣ = 15 := by
    rw [Nat.card_units, GaloisField.card 2 4 (by norm_num)]
    norm_num
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := (GaloisField 2 4)ˣ) 3
    (by rw [hcard]; norm_num)
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := (GaloisField 2 4)ˣ) 5
    (by rw [hcard]; norm_num)
  obtain ⟨hu3, hu1⟩ := orderOf_eq_prime_iff.mp hu
  obtain ⟨hv5, hv1⟩ := orderOf_eq_prime_iff.mp hv
  have hu3' : (u : GaloisField 2 4) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hu3, Units.val_one]
  have hu1' : (u : GaloisField 2 4) ≠ 1 := fun h => hu1 (Units.val_eq_one.mp h)
  have hω : (u : GaloisField 2 4) ^ 2 + u + 1 = 0 := by
    have h : ((u : GaloisField 2 4) - 1) * ((u : GaloisField 2 4) ^ 2 + u + 1) = 0 := by
      linear_combination hu3'
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hu1')
  have hv5' : (v : GaloisField 2 4) ^ 5 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hv5, Units.val_one]
  have hv1' : (v : GaloisField 2 4) ≠ 1 := fun h => hv1 (Units.val_eq_one.mp h)
  exact exists_orderOf_five_commute_sl2189 hω hv5' hv1' hx3 hx1

end CFSG.RankThree.PartTwo.Sec18
