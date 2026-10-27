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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Quasithin

open scoped Matrix

variable {F : Type*} [Field F] {d : ℕ}

@[expose] def swapMap (ϑ : F ≃+* F) (Q R : Matrix (Fin d) (Fin d) F)
    (M : Matrix (Fin d) (Fin d) F) : Matrix (Fin d) (Fin d) F :=
  Q * (M.map ϑ)ᵀ * R

namespace D37Swap

theorem conj_conj_eq (ϑ : F ≃+* F) (N Y : Matrix (Fin d) (Fin d) F) :
    (((Y.map ϑ)ᵀ * N).map ϑ)ᵀ * N = (N.map ϑ)ᵀ * (Y.map ϑ).map ϑ * N := by
  rw [Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_map, Matrix.transpose_transpose]

theorem scalar_of_conj_conj (ϑ : F ≃+* F) {N : Matrix (Fin d) (Fin d) F}
    (h : ∀ Y : Matrix (Fin d) (Fin d) F, (((Y.map ϑ)ᵀ * N).map ϑ)ᵀ * N = Y) :
    N ∈ Set.range (Matrix.scalar (Fin d)) := by
  have h' : ∀ Y : Matrix (Fin d) (Fin d) F, (N.map ϑ)ᵀ * (Y.map ϑ).map ϑ * N = Y := by
    intro Y
    rw [← conj_conj_eq]
    exact h Y
  have h1 : (N.map ϑ)ᵀ * N = 1 := by simpa using h' 1
  have h2 : N * (N.map ϑ)ᵀ = 1 := mul_eq_one_comm.1 h1
  refine Matrix.mem_range_scalar_of_commute_single fun i j _ => ?_
  have h3 := h' (Matrix.single i j 1)
  simp only [Matrix.map_single, map_one] at h3
  show Matrix.single i j 1 * N = N * Matrix.single i j 1
  calc Matrix.single i j 1 * N = (N * (N.map ϑ)ᵀ) * Matrix.single i j 1 * N := by
        rw [h2, Matrix.one_mul]
    _ = N * ((N.map ϑ)ᵀ * Matrix.single i j 1 * N) := by simp only [Matrix.mul_assoc]
    _ = N * Matrix.single i j 1 := by rw [h3]

abbrev UpperIdx (d : ℕ) : Type := {p : Fin d × Fin d // p.1 < p.2}

def upperOf (y : UpperIdx d → F) : Matrix (Fin d) (Fin d) F :=
  Matrix.of fun i j => if h : i < j then y ⟨(i, j), h⟩ else 0

theorem upperOf_apply_lt (y : UpperIdx d → F) {i j : Fin d} (h : i < j) :
    upperOf y i j = y ⟨(i, j), h⟩ := by
  simp [upperOf, h]

theorem upperOf_apply_not_lt (y : UpperIdx d → F) {i j : Fin d} (h : ¬ i < j) :
    upperOf y i j = 0 := by
  simp [upperOf, h]

theorem card_upperIdx (d : ℕ) : Nat.card (UpperIdx d) = d * (d - 1) / 2 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Fintype.card_product_filter_lt,
    Fintype.card_fin, Nat.choose_two_right]

theorem upperOf_injective : Function.Injective (upperOf (F := F) (d := d)) := by
  intro y y' h
  funext p
  have := congrFun (congrFun h p.1.1) p.1.2
  rwa [upperOf_apply_lt y p.2, upperOf_apply_lt y' p.2] at this

theorem conj_upperOf_apply_lt (ϑ : F ≃+* F) (c : F) (y : UpperIdx d → F) {i j : Fin d}
    (h : i < j) :
    (((upperOf y).map ϑ)ᵀ * Matrix.scalar (Fin d) c) i j = 0 := by
  rw [Matrix.scalar_apply, Matrix.mul_diagonal]
  simp [upperOf_apply_not_lt y (not_lt.2 h.le)]

end D37Swap

open D37Swap

theorem card_range_one_add_swap [Finite F] (ϑ : F ≃+* F) (Q R : Matrix (Fin d) (Fin d) F)
    (hQ : IsUnit Q)
    (h2 : ∀ M : Matrix (Fin d) (Fin d) F, swapMap ϑ Q R (swapMap ϑ Q R M) = M) :
    Nat.card F ^ (d * (d - 1) / 2) ≤
      Nat.card (Set.range fun M : Matrix (Fin d) (Fin d) F => M + swapMap ϑ Q R M) := by
  set N : Matrix (Fin d) (Fin d) F := (Q.map ϑ)ᵀ * R with hN
  have hconj : ∀ Y : Matrix (Fin d) (Fin d) F,
      Q * ((Y.map ϑ)ᵀ * N) = swapMap ϑ Q R (Q * Y) := by
    intro Y
    simp only [swapMap, hN, Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]
  have hΛ2 : ∀ Y : Matrix (Fin d) (Fin d) F, (((Y.map ϑ)ᵀ * N).map ϑ)ᵀ * N = Y := by
    intro Y
    apply (hQ.mul_right_inj).1
    rw [hconj, hconj, h2]
  obtain ⟨c, hc⟩ := scalar_of_conj_conj ϑ hΛ2
  let δ : Matrix (Fin d) (Fin d) F → Matrix (Fin d) (Fin d) F := fun M => M + swapMap ϑ Q R M
  let f : (UpperIdx d → F) → Set.range δ := fun y => ⟨δ (Q * upperOf y), _, rfl⟩
  have hf : Function.Injective f := by
    intro y y' hyy
    have h1 : δ (Q * upperOf y) = δ (Q * upperOf y') := congrArg Subtype.val hyy
    have h3 : ∀ z, δ (Q * upperOf z) = Q * (upperOf z + (((upperOf z).map ϑ)ᵀ * N)) := by
      intro z
      simp only [δ, ← hconj, Matrix.mul_add]
    rw [h3, h3] at h1
    have h4 := (hQ.mul_right_inj).1 h1
    apply upperOf_injective
    ext i j
    by_cases hij : i < j
    · have := congrFun (congrFun h4 i) j
      rw [Matrix.add_apply, Matrix.add_apply, ← hc, conj_upperOf_apply_lt ϑ c y hij,
        conj_upperOf_apply_lt ϑ c y' hij] at this
      simpa using this
    · rw [upperOf_apply_not_lt y hij, upperOf_apply_not_lt y' hij]
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_fun, card_upperIdx] at this

end CFSG.Quasithin
