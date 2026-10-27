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
public import Mathlib.LinearAlgebra.Matrix.Rank
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

namespace CFSG.RankThree.PartTwo.Sec19.NF5Pair
open Matrix

theorem not_span_pair_eq_top {F : Type*} [Field F] (p q : Fin 3 → F)
    (h : ∀ x : Fin 3 → F, x ∈ Submodule.span F ({p, q} : Set (Fin 3 → F))) : False := by
  classical
  have hcoe : (({p, q} : Finset (Fin 3 → F)) : Set (Fin 3 → F)) = {p, q} := by simp
  have h1 : Module.finrank F (Submodule.span F ({p, q} : Set (Fin 3 → F))) ≤ 2 := by
    rw [← hcoe]
    exact (finrank_span_finset_le_card (R := F) ({p, q} : Finset (Fin 3 → F))).trans
      Finset.card_le_two
  have h3 : Submodule.span F ({p, q} : Set (Fin 3 → F)) = ⊤ :=
    Submodule.eq_top_iff'.2 h
  rw [h3, finrank_top, Module.finrank_fin_fun] at h1
  omega

theorem no_commute_homol_heis {F : Type*} [Field F] (g h : Matrix (Fin 3) (Fin 3) F)
    (hg : IsUnit g) (hh : IsUnit h) (a : F) (u v : Fin 3 → F) (hu : u ≠ 0) (hv : v ≠ 0)
    (hgav : g = a • (1 : Matrix (Fin 3) (Fin 3) F) + Matrix.vecMulVec u v)
    (hheis : ∀ (w : Fin 3 → F) (θ : F), w ≠ 0 → h.mulVec w ≠ θ • w)
    (c : F) (hcomm : g * h = c • (h * g)) : False := by
  classical
  have e1 : g * h = a • h + Matrix.vecMulVec u (v ᵥ* h) := by
    rw [hgav, add_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.vecMulVec_mul]
  have e2 : h * g = a • h + Matrix.vecMulVec (h *ᵥ u) v := by
    rw [hgav, mul_add, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_vecMulVec]
  rw [e1, e2] at hcomm
  have key : ∀ i j, ((1 - c) * a) * h i j =
      c * ((h *ᵥ u) i * v j) - u i * (v ᵥ* h) j := by
    intro i j
    have := congrFun (congrFun hcomm i) j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul] at this
    linear_combination this
  by_cases hca : (1 - c) * a = 0
  ·
    have ha : a ≠ 0 := by
      rintro rfl
      have hg1 : g = Matrix.vecMulVec u v := by simpa using hgav
      have h1 := Matrix.rank_vecMulVec_le u v
      rw [← hg1, Matrix.rank_of_isUnit g hg] at h1
      simp at h1
    have hc : c = 1 := by
      have := (mul_eq_zero.1 hca).resolve_right ha
      exact (sub_eq_zero.1 this).symm
    subst hc
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
    have hi' : v i ≠ 0 := hi
    have h1 : ∀ k j, (h *ᵥ u) k * v j = u k * (v ᵥ* h) j := by
      intro k j
      have := key k j
      rw [hca] at this
      linear_combination (-1 : F) * this
    refine hheis u (((v ᵥ* h) i) / v i) hu ?_
    ext k
    have h2 := h1 k i
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
    linear_combination h2
  ·
    apply not_span_pair_eq_top (h *ᵥ u) u
    intro x
    have hd := (Matrix.isUnit_iff_isUnit_det h).1 hh
    have hmul : h * h⁻¹ = 1 := Matrix.mul_nonsing_inv h hd
    obtain ⟨w, hhw⟩ : ∃ w : Fin 3 → F, h *ᵥ w = x :=
      ⟨h⁻¹ *ᵥ x, by rw [Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec]⟩
    subst hhw
    generalize hp : h *ᵥ u = p at key ⊢
    generalize hq : v ᵥ* h = r at key
    rw [Submodule.mem_span_pair]
    refine ⟨((1 - c) * a)⁻¹ * c * (v ⬝ᵥ w), -(((1 - c) * a)⁻¹ * (r ⬝ᵥ w)), ?_⟩
    ext k
    have hk : ((1 - c) * a) * (h *ᵥ w) k = c * p k * (v ⬝ᵥ w) - u k * (r ⬝ᵥ w) := by
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      linear_combination w j * key k j
    have hw' : (h *ᵥ w) k = ((1 - c) * a)⁻¹ * (c * p k * (v ⬝ᵥ w) - u k * (r ⬝ᵥ w)) := by
      rw [← hk, ← mul_assoc, inv_mul_cancel₀ hca, one_mul]
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, hw']
    ring

end CFSG.RankThree.PartTwo.Sec19.NF5Pair