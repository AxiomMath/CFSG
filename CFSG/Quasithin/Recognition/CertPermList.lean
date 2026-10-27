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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Quasithin

@[expose] def RepL {n : ℕ} (l : List ℕ) (σ : Equiv.Perm (Fin n)) : Prop :=
  l.length = n ∧ ∀ i : Fin n, l.getD i 0 = (σ i : ℕ)

instance {n : ℕ} (l : List ℕ) (σ : Equiv.Perm (Fin n)) : Decidable (RepL l σ) := by
  unfold RepL
  infer_instance

@[expose] def compL (l m : List ℕ) : List ℕ := m.map fun j => l.getD j 0

theorem repL_mul {n : ℕ} {l m : List ℕ} {σ τ : Equiv.Perm (Fin n)} (hl : RepL l σ)
    (hm : RepL m τ) : RepL (compL l m) (σ * τ) := by
  refine ⟨by simp [compL, hm.1], fun i => ?_⟩
  have hi : (i : ℕ) < m.length := by rw [hm.1]; exact i.2
  have h1 : (compL l m).getD i 0 = l.getD (m.getD i 0) 0 := by
    simp only [compL, List.getD_eq_getElem _ _ hi, List.getD_eq_getElem?_getD]
    simp [List.getElem?_eq_getElem hi]
  rw [h1, hm.2 i]
  exact hl.2 (τ i)

theorem repL_one (n : ℕ) : RepL (List.range n) (1 : Equiv.Perm (Fin n)) := by
  refine ⟨by simp, fun i => ?_⟩
  simp

theorem repL_unique {n : ℕ} {l l' : List ℕ} {σ : Equiv.Perm (Fin n)} (h : RepL l σ)
    (h' : RepL l' σ) : l = l' := by
  apply List.ext_getElem (h.1.trans h'.1.symm)
  intro i hi hi'
  have hn : i < n := h.1 ▸ hi
  have e1 := h.2 ⟨i, hn⟩
  have e2 := h'.2 ⟨i, hn⟩
  rw [List.getD_eq_getElem _ _ hi] at e1
  rw [List.getD_eq_getElem _ _ hi'] at e2
  exact e1.trans e2.symm

theorem eq_of_repL {n : ℕ} {l : List ℕ} {σ τ : Equiv.Perm (Fin n)} (hσ : RepL l σ)
    (hτ : RepL l τ) : σ = τ := by
  ext i
  have e1 := hσ.2 i
  have e2 := hτ.2 i
  exact e1.symm.trans e2

theorem ne_of_repL_ne {n : ℕ} {l l' : List ℕ} {σ τ : Equiv.Perm (Fin n)} (hσ : RepL l σ)
    (hτ : RepL l' τ) (h : l ≠ l') : σ ≠ τ := by
  rintro rfl
  exact h (repL_unique hσ hτ)

end CFSG.Quasithin
