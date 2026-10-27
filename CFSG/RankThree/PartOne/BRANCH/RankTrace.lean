module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.Commutator.Finite
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.RankThree.PartOne.BRANCH

open Matrix Module

variable {n : ℕ} {K : Type} [Field K] {P : Type} [Group P]

theorem trace_eq_zero_of_noncentral (ρ : P →* GL (Fin n) K)
    (hρ : Function.Injective ρ)
    (hcomm : ∀ g h : P, ∃ c : Kˣ,
      ρ (g * h * g⁻¹ * h⁻¹) = Matrix.GeneralLinearGroup.scalar (Fin n) c)
    {y : P} (hy : y ∉ Subgroup.center P) :
    Matrix.trace (ρ y : Matrix (Fin n) (Fin n) K) = 0 := by
  have hnc : ∃ x : P, x * y ≠ y * x := by
    by_contra hcon
    push Not at hcon
    apply hy
    rw [Subgroup.mem_center_iff]
    intro g
    exact hcon g
  obtain ⟨x, hxy⟩ := hnc
  obtain ⟨c, hc⟩ := hcomm x y
  have hc1 : (c : K) ≠ 1 := by
    intro h
    have hc' : c = 1 := Units.ext h
    rw [hc', map_one] at hc
    apply hxy
    have h1 : x * y * x⁻¹ * y⁻¹ = 1 := hρ (by rw [hc, map_one])
    calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
      _ = y * x := by rw [h1, one_mul]
  have h1 : ρ x * ρ y * (ρ x)⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin n) c * ρ y := by
    have h0 : ρ x * ρ y * (ρ x)⁻¹ * (ρ y)⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin n) c := by
      rw [← hc]
      simp
    rw [← h0]
    group
  have h2 := congrArg (fun g : GL (Fin n) K => Matrix.trace (g : Matrix (Fin n) (Fin n) K)) h1
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar] at h2
  have h3 : Matrix.trace ((ρ x : Matrix (Fin n) (Fin n) K) * (ρ y : Matrix (Fin n) (Fin n) K) *
      (((ρ x)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) =
      Matrix.trace (ρ y : Matrix (Fin n) (Fin n) K) := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mul]
  rw [h3] at h2
  have h4 : Matrix.trace (Matrix.scalar (Fin n) (c : K) * (ρ y : Matrix (Fin n) (Fin n) K)) =
      (c : K) * Matrix.trace (ρ y : Matrix (Fin n) (Fin n) K) := by
    rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul, Matrix.trace_smul, smul_eq_mul]
  rw [h4] at h2
  have h5 : (1 - (c : K)) * Matrix.trace (ρ y : Matrix (Fin n) (Fin n) K) = 0 := by
    linear_combination h2
  rcases mul_eq_zero.mp h5 with h | h
  · exact absurd (sub_eq_zero.mp h).symm hc1
  · exact h

theorem card_quotient_center_le_sq [Finite P] (ρ : P →* GL (Fin n) K) (hρ : Function.Injective ρ)
    (hnK : (n : K) ≠ 0)
    (hcomm : ∀ g h : P, ∃ c : Kˣ,
      ρ (g * h * g⁻¹ * h⁻¹) = Matrix.GeneralLinearGroup.scalar (Fin n) c) :
    Nat.card (P ⧸ Subgroup.center P) ≤ n ^ 2 := by
  classical
  have : Fintype (P ⧸ Subgroup.center P) := Fintype.ofFinite _
  let s : P ⧸ Subgroup.center P → P := Quotient.out
  have hs : ∀ a, (s a : P ⧸ Subgroup.center P) = a := fun a => Quotient.out_eq' a
  let f : (P ⧸ Subgroup.center P) → Matrix (Fin n) (Fin n) K :=
    fun a => ((ρ (s a) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  have htr : ∀ a b : P ⧸ Subgroup.center P, a ≠ b →
      Matrix.trace (f a * (((ρ (s b))⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = 0 := by
    intro a b hab
    have hnc : s a * (s b)⁻¹ ∉ Subgroup.center P := by
      intro h
      apply hab
      have h1 : ((s a * (s b)⁻¹ : P) : P ⧸ Subgroup.center P) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr h
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hs a, hs b] at h1
      exact mul_inv_eq_one.mp h1
    have := trace_eq_zero_of_noncentral ρ hρ hcomm hnc
    simpa [f] using this
  have hli : LinearIndependent K f := by
    rw [linearIndependent_iff']
    intro t g hsum j hj
    have h1 := congrArg (fun M : Matrix (Fin n) (Fin n) K =>
      Matrix.trace (M * (((ρ (s j))⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) hsum
    simp only [Finset.sum_mul, Matrix.zero_mul, Matrix.trace_zero, Matrix.smul_mul] at h1
    rw [Matrix.trace_sum] at h1
    simp only [Matrix.trace_smul, smul_eq_mul] at h1
    rw [Finset.sum_eq_single_of_mem j hj] at h1
    · have hjj : Matrix.trace (f j * (((ρ (s j))⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) =
          (n : K) := by
        simp [f]
      rw [hjj] at h1
      exact (mul_eq_zero.mp h1).resolve_right hnK
    · intro i _ hij
      rw [htr i j hij, mul_zero]
  have := hli.fintype_card_le_finrank
  rw [Module.finrank_matrix, Module.finrank_self, Fintype.card_fin] at this
  rw [Nat.card_eq_fintype_card]
  nlinarith

end CFSG.RankThree.PartOne.BRANCH
