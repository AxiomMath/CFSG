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
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
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
public import Mathlib.Topology.Sheaves.Init

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.Vol2.A128.Lin

theorem exists_ne_zero_dot_eq_zero {n : ℕ} (X : Finset (Fin n → ZMod 2)) (hX : X.card < n) :
    ∃ x : Fin n → ZMod 2, x ≠ 0 ∧ ∀ l ∈ X, l ⬝ᵥ x = 0 := by
  let f : (Fin n → ZMod 2) →ₗ[ZMod 2] (X → ZMod 2) :=
    { toFun := fun x l => l.1 ⬝ᵥ x
      map_add' := fun x y => by ext l; simp [dotProduct_add]
      map_smul' := fun c x => by ext l; simp [dotProduct_smul] }
  have hker : LinearMap.ker f ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hX)
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  exact ⟨x, hx0, fun l hl => congrFun (LinearMap.mem_ker.mp hx) ⟨l, hl⟩⟩

theorem exists_dot_eq_one_of_three_aux : ∀ X : Finset (Fin 3 → ZMod 2),
    (∀ x : Fin 3 → ZMod 2, x ≠ 0 → ∃ l ∈ X, l ⬝ᵥ x = 1) →
    (∀ x : Fin 3 → ZMod 2, x ≠ 0 → (X.filter fun l => l ⬝ᵥ x = 0).card ≤ 2) →
    ∃ x : Fin 3 → ZMod 2, x ≠ 0 ∧ ∀ l ∈ X, l ⬝ᵥ x = 1 := by
  set_option synthInstance.maxSize 2000 in
  decide +kernel

theorem le_three_of_dot {n : ℕ} (X : Finset (Fin n → ZMod 2))
    (h1 : ∀ x : Fin n → ZMod 2, x ≠ 0 → ∃ l ∈ X, l ⬝ᵥ x = 1)
    (h2 : ∀ x : Fin n → ZMod 2, x ≠ 0 → (X.filter fun l => l ⬝ᵥ x = 0).card ≤ 2) : n ≤ 3 := by
  by_contra hn
  push Not at hn
  have hcard : 3 ≤ X.card := by
    by_contra hlt
    push Not at hlt
    obtain ⟨x, hx, hx0⟩ := exists_ne_zero_dot_eq_zero X (by omega)
    obtain ⟨l, hl, hl1⟩ := h1 x hx
    have h := hx0 l hl
    rw [hl1] at h
    exact absurd h (by decide)
  obtain ⟨Y, hYX, hY⟩ := Finset.exists_subset_card_eq hcard
  obtain ⟨x, hx, hx0⟩ := exists_ne_zero_dot_eq_zero Y (by omega)
  have hsub : Y ⊆ X.filter fun l => l ⬝ᵥ x = 0 := fun l hl =>
    Finset.mem_filter.mpr ⟨hYX hl, hx0 l hl⟩
  have := (Finset.card_le_card hsub).trans (h2 x hx)
  omega

theorem exists_dot_eq_one_of_three {n : ℕ} (hn : n = 3) (X : Finset (Fin n → ZMod 2))
    (h1 : ∀ x : Fin n → ZMod 2, x ≠ 0 → ∃ l ∈ X, l ⬝ᵥ x = 1)
    (h2 : ∀ x : Fin n → ZMod 2, x ≠ 0 → (X.filter fun l => l ⬝ᵥ x = 0).card ≤ 2) :
    ∃ x : Fin n → ZMod 2, x ≠ 0 ∧ ∀ l ∈ X, l ⬝ᵥ x = 1 := by
  subst hn
  exact exists_dot_eq_one_of_three_aux X h1 h2

end CFSG.Quasithin.Vol2.A128.Lin
