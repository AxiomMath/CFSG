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
public import Mathlib.RingTheory.Radical.NatInt
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

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.Vol2.A128.Lin

variable (F : Type*) [Field F] {n : ℕ}

def sgn (a : ZMod 2) : F := if a = 0 then 1 else -1

def chi (l x : Fin n → ZMod 2) : F := sgn F (l ⬝ᵥ x)

variable {F}

theorem zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a; decide

theorem vec_add_self (y : Fin n → ZMod 2) : y + y = 0 := by
  ext i; exact CharTwo.add_self_eq_zero _

theorem vec_add_add_self (x y : Fin n → ZMod 2) : y + (y + x) = x := by
  rw [← add_assoc, vec_add_self, zero_add]

theorem vec_add_eq_zero_iff {a b : Fin n → ZMod 2} : a + b = 0 ↔ a = b :=
  ⟨fun h => calc a = b + (b + a) := (vec_add_add_self a b).symm
      _ = b + (a + b) := by rw [add_comm a b]
      _ = b := by rw [h, add_zero],
    fun h => h ▸ vec_add_self a⟩

theorem sgn_zero : sgn F 0 = 1 := by simp [sgn]

theorem sgn_one : sgn F 1 = -1 := by
  have : (1 : ZMod 2) ≠ 0 := by decide
  simp [sgn, this]

theorem sgn_add (a b : ZMod 2) : sgn F (a + b) = sgn F a * sgn F b := by
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rcases zmod_two_cases a with rfl | rfl <;> rcases zmod_two_cases b with rfl | rfl <;>
    simp [sgn_zero, sgn_one, h11]

theorem chi_zero_left (x : Fin n → ZMod 2) : chi F 0 x = 1 := by
  simp [chi, sgn_zero]

theorem chi_add_right (l x y : Fin n → ZMod 2) : chi F l (x + y) = chi F l x * chi F l y := by
  simp [chi, dotProduct_add, sgn_add]

theorem chi_add_left (l l' x : Fin n → ZMod 2) : chi F (l + l') x = chi F l x * chi F l' x := by
  simp [chi, add_dotProduct, sgn_add]

theorem chi_comm (l x : Fin n → ZMod 2) : chi F l x = chi F x l := by
  simp [chi, dotProduct_comm]

theorem chi_eq_one {l x : Fin n → ZMod 2} (h : l ⬝ᵥ x = 0) : chi F l x = 1 := by
  simp [chi, h, sgn_zero]

theorem chi_eq_neg_one {l x : Fin n → ZMod 2} (h : l ⬝ᵥ x = 1) : chi F l x = -1 := by
  simp [chi, h, sgn_one]

theorem sum_chi_right (h2 : (2 : F) ≠ 0) (l : Fin n → ZMod 2) :
    ∑ x : Fin n → ZMod 2, chi F l x = if l = 0 then (2 : F) ^ n else 0 := by
  by_cases hl : l = 0
  · subst hl
    simp [chi_zero_left]
  · simp only [hl, ↓reduceIte]
    obtain ⟨i, hi⟩ : ∃ i, l i ≠ 0 := by
      by_contra hcon
      exact hl (funext fun i => by simpa using not_exists.mp hcon i)
    have hli : l i = 1 := (zmod_two_cases _).resolve_left hi
    obtain ⟨x0, hx0⟩ : ∃ x0 : Fin n → ZMod 2, chi F l x0 = -1 :=
      ⟨Pi.single i 1, chi_eq_neg_one (by simp [dotProduct_single, hli])⟩
    have hS : ∑ x : Fin n → ZMod 2, chi F l x = -∑ x : Fin n → ZMod 2, chi F l x := by
      have h := Equiv.sum_comp (Equiv.addRight x0) (chi F l)
      simp only [Equiv.coe_addRight, chi_add_right, hx0, mul_neg, mul_one,
        Finset.sum_neg_distrib] at h
      exact h.symm
    have h2S : (2 : F) * ∑ x : Fin n → ZMod 2, chi F l x = 0 := by
      rw [two_mul]; nth_rewrite 1 [hS]; exact neg_add_cancel _
    exact (mul_eq_zero.mp h2S).resolve_left h2

theorem sum_chi_left (h2 : (2 : F) ≠ 0) (x : Fin n → ZMod 2) :
    ∑ l : Fin n → ZMod 2, chi F l x = if x = 0 then (2 : F) ^ n else 0 := by
  simp_rw [chi_comm _ x]
  exact sum_chi_right h2 x

end CFSG.Quasithin.Vol2.A128.Lin
