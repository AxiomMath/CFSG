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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Sporadic.Ly

open Matrix

variable {K : Type*} [Field K] {d r : ℕ}

@[expose] def IsRREF (U : Matrix (Fin d) (Fin r) K) (p : Fin r → Fin d) : Prop :=
  StrictMono p ∧ (∀ l m, U (p l) m = if l = m then 1 else 0) ∧ ∀ m (j : Fin d), j < p m → U j m = 0

theorem isRREF_mulVec {U : Matrix (Fin d) (Fin r) K} {p : Fin r → Fin d} (hU : IsRREF U p)
    (c : Fin r → K) (k₀ : Fin r) (hc : ∀ k < k₀, c k = 0) :
    (∀ j < p k₀, (U *ᵥ c) j = 0) ∧ (U *ᵥ c) (p k₀) = c k₀ := by
  obtain ⟨hmono, hid, hzero⟩ := hU
  refine ⟨fun j hj => ?_, ?_⟩
  · simp only [mulVec, dotProduct]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge k k₀ with hk | hk
    · rw [hc k hk, mul_zero]
    · rw [hzero k j (lt_of_lt_of_le hj (hmono.monotone hk)), zero_mul]
  · simp only [mulVec, dotProduct, hid]
    rw [Finset.sum_eq_single k₀ (fun k _ hk => by simp [Ne.symm hk])
      (fun h => absurd (Finset.mem_univ _) h)]
    simp

theorem pivot_mem_range {U : Matrix (Fin d) (Fin r) K} {p : Fin r → Fin d} (hU : IsRREF U p)
    {s : ℕ} {V : Matrix (Fin d) (Fin s) K} {q : Fin s → Fin d} (hV : IsRREF V q)
    {X : Matrix (Fin r) (Fin s) K} (hVX : V = U * X) (m : Fin s) : ∃ k, p k = q m := by
  classical
  have hcol : ∀ j, V j m = (U *ᵥ fun k => X k m) j := by
    intro j; rw [hVX]; simp [mul_apply, mulVec, dotProduct]
  have hne : ∃ k, X k m ≠ 0 := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    have h1 : V (q m) m = 1 := by rw [hV.2.1]; simp
    rw [hcol] at h1
    simp [mulVec, dotProduct, hall] at h1
  let k₀ := Finset.min' (Finset.univ.filter fun k => X k m ≠ 0) (by
    obtain ⟨k, hk⟩ := hne; exact ⟨k, by simp [hk]⟩)
  have hk₀ : X k₀ m ≠ 0 := by
    have := Finset.min'_mem (Finset.univ.filter fun k => X k m ≠ 0) (by
      obtain ⟨k, hk⟩ := hne; exact ⟨k, by simp [hk]⟩)
    simpa using this
  have hbelow : ∀ k < k₀, X k m = 0 := by
    intro k hk
    by_contra h
    have := Finset.min'_le (Finset.univ.filter fun k => X k m ≠ 0) k (by simp [h])
    exact absurd hk (not_lt.2 this)
  obtain ⟨hz, hlead⟩ := isRREF_mulVec hU (fun k => X k m) k₀ hbelow
  refine ⟨k₀, le_antisymm ?_ ?_⟩
  ·
    by_contra h
    have h1 : V (q m) m = 1 := by rw [hV.2.1]; simp
    rw [hcol, hz _ (not_le.1 h)] at h1
    exact zero_ne_one h1
  ·
    by_contra h
    have := hV.2.2 m (p k₀) (not_le.1 h)
    rw [hcol, hlead] at this
    exact hk₀ this

theorem strictMono_eq_of_range {p q : Fin r → Fin d} (hp : StrictMono p) (hq : StrictMono q)
    (h : ∀ m, ∃ k, p k = q m) : p = q := by
  classical
  choose f hf using h
  have hfmono : StrictMono f := by
    intro a b hab
    have : p (f a) < p (f b) := by rw [hf, hf]; exact hq hab
    exact hp.lt_iff_lt.1 this
  have hfid : ∀ m, f m = m := fun m => hfmono.apply_eq
  funext m
  rw [← hf m, hfid m]

theorem eq_of_isRREF {U U' : Matrix (Fin d) (Fin r) K} {p p' : Fin r → Fin d} (hU : IsRREF U p)
    (hU' : IsRREF U' p') {X : Matrix (Fin r) (Fin r) K} (h : U' = U * X) : U = U' := by
  have hpp : p = p' := strictMono_eq_of_range hU.1 hU'.1 (pivot_mem_range hU hU' h)
  subst hpp
  have hX : X = 1 := by
    ext l m
    have e := congrFun (congrFun h (p l)) m
    rw [hU'.2.1, mul_apply] at e
    simp only [hU.2.1, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true] at e
    rw [one_apply, ← e]
  rw [h, hX, Matrix.mul_one]

@[expose] def pivSel (K : Type*) [Zero K] [One K] (p : Fin r → Fin d) :
    Matrix (Fin r) (Fin d) K :=
  Matrix.of fun m j => if j = p m then 1 else 0

theorem pivSel_mul {U : Matrix (Fin d) (Fin r) K} {p : Fin r → Fin d} (hU : IsRREF U p) :
    pivSel K p * U = 1 := by
  ext l m
  rw [mul_apply, one_apply]
  simp only [pivSel, of_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
  rw [hU.2.1]

theorem eq_of_isRREF_tensor {U U' : Matrix (Fin d) (Fin r) K} {p p' : Fin r → Fin d}
    (hU : IsRREF U p) (hU' : IsRREF U' p') {S S' : Matrix (Fin r) (Fin r) K}
    {Si : Matrix (Fin r) (Fin r) K} (hS : S * Si = 1)
    (h : U * S * Uᵀ = U' * S' * U'ᵀ) : U = U' ∧ S = S' := by
  have hsel : Uᵀ * (pivSel K p)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, pivSel_mul hU, Matrix.transpose_one]
  have hUS : U * S = U' * (S' * U'ᵀ * (pivSel K p)ᵀ) := by
    calc U * S = U * S * (Uᵀ * (pivSel K p)ᵀ) := by rw [hsel, Matrix.mul_one]
      _ = U * S * Uᵀ * (pivSel K p)ᵀ := by simp only [Matrix.mul_assoc]
      _ = U' * S' * U'ᵀ * (pivSel K p)ᵀ := by rw [h]
      _ = U' * (S' * U'ᵀ * (pivSel K p)ᵀ) := by simp only [Matrix.mul_assoc]
  have hU1 : U = U' * (S' * U'ᵀ * (pivSel K p)ᵀ * Si) := by
    calc U = U * S * Si := by rw [Matrix.mul_assoc, hS, Matrix.mul_one]
      _ = U' * (S' * U'ᵀ * (pivSel K p)ᵀ * Si) := by rw [hUS, Matrix.mul_assoc]
  have hUU : U' = U := eq_of_isRREF hU' hU hU1
  rw [hUU] at h
  refine ⟨hUU.symm, ?_⟩
  have e := congrArg (fun M => pivSel K p * M * (pivSel K p)ᵀ) h
  have hl : ∀ T : Matrix (Fin r) (Fin r) K, pivSel K p * (U * T * Uᵀ) * (pivSel K p)ᵀ = T := by
    intro T
    calc pivSel K p * (U * T * Uᵀ) * (pivSel K p)ᵀ =
          (pivSel K p * U) * T * (Uᵀ * (pivSel K p)ᵀ) := by
          simp only [Matrix.mul_assoc]
      _ = T := by rw [pivSel_mul hU, hsel, Matrix.one_mul, Matrix.mul_one]
  rw [hl, hl] at e
  exact e

end CFSG.Sporadic.Ly
