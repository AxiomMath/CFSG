module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
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

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecJ

open Matrix
open scoped Matrix

variable {F : Type*} [Field F]

theorem det_smul_one_add_smul (M : Matrix (Fin 2) (Fin 2) F) (a b : F) :
    (a • (1 : Matrix (Fin 2) (Fin 2) F) + b • M).det =
      a ^ 2 + a * b * M.trace + b ^ 2 * M.det := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two, Matrix.trace_fin_two]
  simp
  ring

theorem mul_self_eq_trace (M : Matrix (Fin 2) (Fin 2) F) :
    M * M = M.trace • M - M.det • (1 : Matrix (Fin 2) (Fin 2) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring

theorem exists_eq_of_commute {M X : Matrix (Fin 2) (Fin 2) F}
    (hM : ∀ c : F, M ≠ c • (1 : Matrix (Fin 2) (Fin 2) F)) (hX : X * M = M * X) :
    ∃ a b : F, X = a • (1 : Matrix (Fin 2) (Fin 2) F) + b • M := by
  have e : ∀ i j, (X * M) i j = (M * X) i j := fun i j => by rw [hX]
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10
  by_cases h01 : M 0 1 = 0
  · by_cases h10 : M 1 0 = 0
    · have hd : M 0 0 - M 1 1 ≠ 0 := by
        intro hd
        apply hM (M 0 0)
        ext i j
        fin_cases i <;> fin_cases j <;> simp [h01, h10]
        linear_combination -hd
      have hx01 : X 0 1 = 0 := by
        have : X 0 1 * (M 0 0 - M 1 1) = 0 := by rw [h01] at e01; linear_combination -e01
        exact (mul_eq_zero.1 this).resolve_right hd
      have hx10 : X 1 0 = 0 := by
        have : X 1 0 * (M 0 0 - M 1 1) = 0 := by rw [h10] at e10; linear_combination e10
        exact (mul_eq_zero.1 this).resolve_right hd
      refine ⟨X 0 0 - (X 0 0 - X 1 1) / (M 0 0 - M 1 1) * M 0 0,
        (X 0 0 - X 1 1) / (M 0 0 - M 1 1), ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h01, h10, hx01, hx10]
      field_simp
      ring
    · refine ⟨X 0 0 - X 1 0 / M 1 0 * M 0 0, X 1 0 / M 1 0, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp
      · field_simp
        linear_combination e00
      · field_simp
      · field_simp
        linear_combination e10
  · refine ⟨X 0 0 - X 0 1 / M 0 1 * M 0 0, X 0 1 / M 0 1, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    · field_simp
    · field_simp
      linear_combination -e00
    · field_simp
      linear_combination -e01

theorem det_ne_zero_of_orderOf [Finite F] [CharP F 2] {y : GL (Fin 2) F} (hy : y ≠ 1)
    (hodd : Odd (orderOf y)) (hcop : Nat.Coprime (orderOf y) (Nat.card F - 1)) {a b : F}
    (hab : ¬ (a = 0 ∧ b = 0)) :
    (a • (1 : Matrix (Fin 2) (Fin 2) F) + b • (y : Matrix (Fin 2) (Fin 2) F)).det ≠ 0 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hroot : ∀ ζ : F, ζ ≠ 0 → ζ ^ orderOf y = 1 → ζ = 1 := by
    intro ζ hζ hζm
    have h1 : ζ ^ (Nat.card F - 1) = 1 := by
      rw [Nat.card_eq_fintype_card]
      exact FiniteField.pow_card_sub_one_eq_one ζ hζ
    have h3 : ζ ^ Nat.gcd (orderOf y) (Nat.card F - 1) = 1 := pow_gcd_eq_one.2 ⟨hζm, h1⟩
    rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at h3
  set Y : Matrix (Fin 2) (Fin 2) F := (y : Matrix (Fin 2) (Fin 2) F) with hY
  have hYm : Y ^ orderOf y = 1 := by
    rw [hY, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]
  have hdet0 : Y.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp y.isUnit).ne_zero
  have hδ : Y.det = 1 := hroot _ hdet0 (by rw [← Matrix.det_pow, hYm, Matrix.det_one])
  intro hdet
  by_cases hb : b = 0
  · have ha : a ≠ 0 := fun ha => hab ⟨ha, hb⟩
    rw [det_smul_one_add_smul, hb] at hdet
    simp only [mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      zero_mul] at hdet
    exact ha (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.1 hdet)
  · have heq : a • (1 : Matrix (Fin 2) (Fin 2) F) + b • Y = b • (Y - (-a / b) • 1) := by
      rw [smul_sub, smul_smul, mul_div_cancel₀ _ hb, neg_smul, sub_neg_eq_add, add_comm]
    have hsing : (Y - (-a / b) • 1).det = 0 := by
      rw [heq, Matrix.det_smul] at hdet
      exact (mul_eq_zero.1 hdet).resolve_left (pow_ne_zero _ hb)
    set ζ : F := -a / b with hζ
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hsing
    have hYv : Y *ᵥ v = ζ • v := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hv
      exact hv
    have hpow : ∀ k : ℕ, (Y ^ k) *ᵥ v = ζ ^ k • v := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ, ← Matrix.mulVec_mulVec, hYv, Matrix.mulVec_smul, ih, smul_smul, ← pow_succ']
    have hζm : ζ ^ orderOf y = 1 := by
      have h1 := hpow (orderOf y)
      rw [hYm, Matrix.one_mulVec] at h1
      by_contra hne
      apply hv0
      have h3 : (ζ ^ orderOf y - 1) • v = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
      exact (smul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hne)
    have hζ0 : ζ ≠ 0 := by
      intro h0
      rw [h0, zero_smul] at hYv
      exact hv0 (Matrix.eq_zero_of_mulVec_eq_zero hdet0 hYv)
    have hζ1 : ζ = 1 := hroot ζ hζ0 hζm
    have hτ : Y.trace = 0 := by
      have h3 := det_smul_one_add_smul Y (-1) 1
      have h4 : (-1 : F) • (1 : Matrix (Fin 2) (Fin 2) F) + (1 : F) • Y = Y - ζ • 1 := by
        rw [hζ1, neg_smul, one_smul, one_smul]
        abel
      rw [h4, hsing, hδ] at h3
      linear_combination h3 + h2
    have hy2 : y ^ 2 = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one, pow_two, ← hY, mul_self_eq_trace, hτ, hδ]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
      all_goals linear_combination -h2
    have hdvd := orderOf_dvd_of_pow_eq_one hy2
    have h1 : orderOf y = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
      · exact h
      · rw [h] at hodd
        exact absurd hodd (by decide)
    exact hy (orderOf_eq_one_iff.1 h1)

end CFSG.Quasithin.Vol2.Ch11.SecJ
