module

import CFSG.Dihedral.GorensteinWalter.PGL2SquareRange
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
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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

open scoped MatrixGroups
open Matrix.GeneralLinearGroup

namespace CFSG.SignalizerFunctorTheorem.McBride.PSL2Three

variable (K : Type*) [Field K]

@[expose] def transvecUp : SL(2, K) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def transvecLow : SL(2, K) := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩

variable {K}

theorem exists_scalar_of_conj_eq {G : GL (Fin 2) K} {A : SL(2, K)}
    (h : Matrix.ProjGenLinGroup.mk G * Matrix.ProjectiveSpecialLinearGroup.toPGL
        (QuotientGroup.mk A) * (Matrix.ProjGenLinGroup.mk G)⁻¹ =
      Matrix.ProjectiveSpecialLinearGroup.toPGL (QuotientGroup.mk A)) :
    ∃ u : Kˣ, G * Matrix.SpecialLinearGroup.toGL A * scalar (Fin 2) u =
      Matrix.SpecialLinearGroup.toGL A * G := by
  rw [Matrix.ProjectiveSpecialLinearGroup.toPGL_mk, ← map_inv, ← map_mul, ← map_mul,
    Matrix.ProjGenLinGroup.mk_eq_mk_iff] at h
  obtain ⟨u, hu⟩ := h
  refine ⟨u, ?_⟩
  have hs : scalar (Fin 2) u * G = G * scalar (Fin 2) u := scalar_commute u G
  calc G * Matrix.SpecialLinearGroup.toGL A * scalar (Fin 2) u
      = G * Matrix.SpecialLinearGroup.toGL A * (G⁻¹ * (scalar (Fin 2) u * G)) := by
        rw [hs]; group
    _ = (G * Matrix.SpecialLinearGroup.toGL A * G⁻¹ * scalar (Fin 2) u) * G := by group
    _ = Matrix.SpecialLinearGroup.toGL A * G := by rw [hu]

theorem eq_one_of_conj_transvecs {y : PGL(2, K)}
    (h1 : y * Matrix.ProjectiveSpecialLinearGroup.toPGL (QuotientGroup.mk (transvecUp K)) *
      y⁻¹ = Matrix.ProjectiveSpecialLinearGroup.toPGL (QuotientGroup.mk (transvecUp K)))
    (h2 : y * Matrix.ProjectiveSpecialLinearGroup.toPGL (QuotientGroup.mk (transvecLow K)) *
      y⁻¹ = Matrix.ProjectiveSpecialLinearGroup.toPGL (QuotientGroup.mk (transvecLow K))) :
    y = 1 := by
  induction y using Matrix.ProjGenLinGroup.induction_on with | mk G =>
  obtain ⟨u, hu⟩ := exists_scalar_of_conj_eq h1
  obtain ⟨v, hv⟩ := exists_scalar_of_conj_eq h2
  have hu' := congrArg Units.val hu
  have hv' := congrArg Units.val hv
  simp only [Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, coe_scalar] at hu' hv'
  have h00 := congrFun (congrFun hu' 0) 0
  have h01 := congrFun (congrFun hu' 0) 1
  have h10 := congrFun (congrFun hu' 1) 0
  have k00 := congrFun (congrFun hv' 0) 0
  have k01 := congrFun (congrFun hv' 0) 1
  simp only [transvecUp, transvecLow, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.scalar_apply] at h00 h01 h10 k00 k01
  simp at h00 h01 h10 k00 k01
  have hdet : (G : Matrix (Fin 2) (Fin 2) K) 0 0 * G 1 1 - G 0 1 * G 1 0 ≠ 0 := by
    have := Matrix.GeneralLinearGroup.det_ne_zero G
    rwa [Matrix.det_fin_two] at this
  have hc : (G : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    by_contra hc
    have hu1 : (u : K) = 1 := by
      have : (G : Matrix (Fin 2) (Fin 2) K) 1 0 * u = G 1 0 * 1 := by rw [h10, mul_one]
      exact mul_left_cancel₀ hc this
    rw [hu1, mul_one] at h00
    exact hc (by linear_combination -h00)
  have hb : (G : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by
    by_contra hb
    have hv1 : (v : K) = 1 := by
      have : (G : Matrix (Fin 2) (Fin 2) K) 0 1 * v = G 0 1 * 1 := by rw [k01, mul_one]
      exact mul_left_cancel₀ hb this
    rw [hv1, mul_one] at k00
    exact hb (by linear_combination k00)
  have ha : (G : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := by
    intro ha
    apply hdet
    rw [ha, hb, hc]; ring
  have hu1 : (u : K) = 1 := by
    rw [hc, add_zero] at h00
    have : (G : Matrix (Fin 2) (Fin 2) K) 0 0 * u = G 0 0 * 1 := by rw [h00, mul_one]
    exact mul_left_cancel₀ ha this
  rw [hu1, hb] at h01
  simp at h01
  rw [Matrix.ProjGenLinGroup.mk_eq_one,
    Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
  refine ⟨G 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, hb, hc, h01]

theorem sq_mem_range_toPGL (y : PGL(2, K)) :
    ∃ x : PSL(2, K), y ^ 2 = Matrix.ProjectiveSpecialLinearGroup.toPGL x :=
  let ⟨x, hx⟩ := CFSG.GorensteinWalter.pgl2_sq_mem_psl2Range y
  ⟨x, hx.symm⟩

end CFSG.SignalizerFunctorTheorem.McBride.PSL2Three
