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
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.LinearAlgebra.Matrix.CharP
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148R

private lemma upperTri_mul {F : Type} [Field F] {M N : Matrix (Fin 3) (Fin 3) F}
    (hM : ∀ i j : Fin 3, j < i → M i j = 0) (hN : ∀ i j : Fin 3, j < i → N i j = 0) :
    ∀ i j : Fin 3, j < i → (M * N) i j = 0 := by
  intro i j hji
  fin_cases i <;> fin_cases j <;> simp_all [Matrix.mul_apply, Fin.sum_univ_three]

private lemma upperTri_mul_diag {F : Type} [Field F] {M N : Matrix (Fin 3) (Fin 3) F}
    (hM : ∀ i j : Fin 3, j < i → M i j = 0) (hN : ∀ i j : Fin 3, j < i → N i j = 0)
    (i : Fin 3) : (M * N) i i = M i i * N i i := by
  fin_cases i <;> simp [Matrix.mul_apply, Fin.sum_univ_three, hM, hN]

private lemma upperTri_four_diag {F : Type} [Field F] {A B A' B' : Matrix (Fin 3) (Fin 3) F}
    (hA : ∀ i j : Fin 3, j < i → A i j = 0) (hB : ∀ i j : Fin 3, j < i → B i j = 0)
    (hA' : ∀ i j : Fin 3, j < i → A' i j = 0) (hB' : ∀ i j : Fin 3, j < i → B' i j = 0)
    (hAA : A * A' = 1) (hBB : B * B' = 1) (i : Fin 3) :
    (A * B * A' * B') i i = 1 := by
  have hAB := upperTri_mul hA hB
  have hABA' := upperTri_mul hAB hA'
  have h1 : A i i * A' i i = 1 := by
    rw [← upperTri_mul_diag hA hA' i, hAA, Matrix.one_apply_eq]
  have h2 : B i i * B' i i = 1 := by
    rw [← upperTri_mul_diag hB hB' i, hBB, Matrix.one_apply_eq]
  rw [upperTri_mul_diag hABA' hB' i, upperTri_mul_diag hAB hA' i, upperTri_mul_diag hA hB i]
  linear_combination (B i i * B' i i) * h1 + h2

private lemma cube_eq_zero_of_strictUpper {F : Type} [Field F] {M : Matrix (Fin 3) (Fin 3) F}
    (hM : ∀ i j : Fin 3, j ≤ i → M i j = 0) : M ^ 3 = 0 := by
  rw [pow_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, hM]

private lemma one_add_pow_three_of_strictUpper {F : Type} [Field F] [CharP F 3]
    {M : Matrix (Fin 3) (Fin 3) F} (hM : ∀ i j : Fin 3, j ≤ i → M i j = 0) :
    (1 + M) ^ 3 = 1 := by
  rw [add_pow_char_of_commute 3 (Commute.one_left M), one_pow,
    cube_eq_zero_of_strictUpper hM, add_zero]

theorem eq_bot_of_upperTri_charThree {F : Type} [Field F] [Finite F] [CharP F 3]
    (Y : Subgroup (GL (Fin 3) F))
    (hY : ∀ y ∈ Y, ∀ i j : Fin 3, j < i → (y : Matrix (Fin 3) (Fin 3) F) i j = 0)
    (hYp : Group.IsPerfect Y) (hY3 : ¬ 3 ∣ Nat.card Y) : Y = ⊥ := by
  have key : ∀ c : GL (Fin 3) F, c ∈ Y →
      (∀ i : Fin 3, (c : Matrix (Fin 3) (Fin 3) F) i i = 1) → c = 1 := by
    intro c hc hdiag
    have hM : ∀ i j : Fin 3, j ≤ i → ((c : Matrix (Fin 3) (Fin 3) F) - 1) i j = 0 := by
      intro i j hji
      rcases hji.lt_or_eq with hlt | heq
      · simp [Matrix.sub_apply, hY c hc i j hlt, Matrix.one_apply_ne hlt.ne']
      · rw [heq, Matrix.sub_apply, hdiag i, Matrix.one_apply_eq, sub_self]
    have hcube : (c : Matrix (Fin 3) (Fin 3) F) ^ 3 = 1 := by
      have h := one_add_pow_three_of_strictUpper hM
      have e : (1 : Matrix (Fin 3) (Fin 3) F) + ((c : Matrix (Fin 3) (Fin 3) F) - 1)
          = (c : Matrix (Fin 3) (Fin 3) F) := by abel
      rwa [e] at h
    have hGL : c ^ 3 = 1 := Units.ext (by simpa using hcube)
    have h3 : (⟨c, hc⟩ : Y) ^ 3 = 1 := Subtype.ext (by simpa using hGL)
    have hord : orderOf (⟨c, hc⟩ : Y) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    have hdvd : orderOf (⟨c, hc⟩ : Y) ∣ Nat.card Y := orderOf_dvd_natCard _
    rcases (Nat.dvd_prime Nat.prime_three).mp hord with h1 | h1
    · have h1' : (⟨c, hc⟩ : Y) = 1 := orderOf_eq_one_iff.mp h1
      simpa using congrArg Subtype.val h1'
    · rw [h1] at hdvd
      exact absurd hdvd hY3
  have hcomm : ⁅Y, Y⁆ ≤ ⊥ := by
    rw [Subgroup.commutator_le]
    intro g₁ h₁ g₂ h₂
    rw [Subgroup.mem_bot]
    refine key _ ?_ ?_
    · exact Y.mul_mem (Y.mul_mem (Y.mul_mem h₁ h₂) (Y.inv_mem h₁)) (Y.inv_mem h₂)
    · intro i
      rw [commutatorElement_def]
      simp only [Units.val_mul]
      exact upperTri_four_diag (hY g₁ h₁) (hY g₂ h₂) (hY g₁⁻¹ (Y.inv_mem h₁))
        (hY g₂⁻¹ (Y.inv_mem h₂)) (Units.mul_inv g₁) (Units.mul_inv g₂) i
  have hperf := Subgroup.isPerfect_iff.mp hYp
  rw [hperf] at hcomm
  exact le_bot_iff.mp hcomm

end CFSG.RankThree.PartTwo.Sec14.Ronan148R

end
