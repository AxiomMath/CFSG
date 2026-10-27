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
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
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

namespace G11

namespace G118

open Equiv

theorem alt_E9_aux (n : ℕ) (a b : Equiv.Perm (Fin n)) (ha : a ∈ alternatingGroup (Fin n))
    (hb : b ∈ alternatingGroup (Fin n)) (hab : a * b = b * a) (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hba : b ≠ a) (hba2 : b ≠ a ^ 2) :
    ∃ a b : alternatingGroup (Fin n), a * b = b * a ∧ a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ a ≠ 1 ∧
      b ≠ 1 ∧ b ≠ a ∧ b ≠ a ^ 2 := by
  refine ⟨⟨a, ha⟩, ⟨b, hb⟩, Subtype.ext hab, Subtype.ext ?_, Subtype.ext ?_, ?_, ?_, ?_, ?_⟩
  · simpa using ha3
  · simpa using hb3
  · intro h
    exact ha1 (congrArg Subtype.val h)
  · intro h
    exact hb1 (congrArg Subtype.val h)
  · intro h
    exact hba (congrArg Subtype.val h)
  · intro h
    exact hba2 (by simpa using congrArg Subtype.val h)

theorem g118_exists_E9_alt {n : ℕ} (hn : n = 6 ∨ n = 8) :
    ∃ a b : alternatingGroup (Fin n), a * b = b * a ∧ a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ a ≠ 1 ∧
      b ≠ 1 ∧ b ≠ a ∧ b ≠ a ^ 2 := by
  rcases hn with rfl | rfl
  · have h1 : swap (0 : Fin 6) 1 * swap 0 2 ∈ alternatingGroup (Fin 6) := by
      rw [Equiv.Perm.mem_alternatingGroup]
      decide
    have h2 : swap (3 : Fin 6) 4 * swap 3 5 ∈ alternatingGroup (Fin 6) := by
      rw [Equiv.Perm.mem_alternatingGroup]
      decide
    exact alt_E9_aux 6 _ _ h1 h2 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
  · have h1 : swap (0 : Fin 8) 1 * swap 0 2 ∈ alternatingGroup (Fin 8) := by
      rw [Equiv.Perm.mem_alternatingGroup]
      decide
    have h2 : swap (3 : Fin 8) 4 * swap 3 5 ∈ alternatingGroup (Fin 8) := by
      rw [Equiv.Perm.mem_alternatingGroup]
      decide
    exact alt_E9_aux 8 _ _ h1 h2 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)

theorem g118_center_alt_five : Subgroup.center ↥(alternatingGroup (Fin 5)) = ⊥ := by
  have : IsSimpleGroup ↥(alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by simp)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (Subgroup.center ↥(alternatingGroup (Fin 5))) with h | h
  · exact h
  · exfalso
    have h1 : swap (0 : Fin 5) 1 * swap 0 2 ∈ alternatingGroup (Fin 5) := by
      rw [Equiv.Perm.mem_alternatingGroup]
      decide
    have h2 : swap (0 : Fin 5) 3 * swap 0 4 ∈ alternatingGroup (Fin 5) := by
      rw [Equiv.Perm.mem_alternatingGroup]
      decide
    have hmem : (⟨_, h1⟩ : ↥(alternatingGroup (Fin 5))) ∈
        Subgroup.center ↥(alternatingGroup (Fin 5)) := by
      rw [h]
      exact Subgroup.mem_top _
    have := Subgroup.mem_center_iff.1 hmem ⟨_, h2⟩
    have h3 := congrArg Subtype.val this
    have h4 : (swap (0 : Fin 5) 3 * swap 0 4) * (swap 0 1 * swap 0 2) ≠
        (swap 0 1 * swap 0 2) * (swap 0 3 * swap 0 4) := by decide
    exact h4 h3

theorem g118_exists_S3_alt_five :
    ∃ s t : alternatingGroup (Fin 5), t * t = 1 ∧ t ≠ 1 ∧ s ^ 3 = 1 ∧ s ≠ 1 ∧
      t * s * t⁻¹ = s⁻¹ := by
  have h1 : swap (0 : Fin 5) 1 * swap 0 2 ∈ alternatingGroup (Fin 5) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide
  have h2 : swap (0 : Fin 5) 1 * swap 3 4 ∈ alternatingGroup (Fin 5) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide
  have e1 : (swap (0 : Fin 5) 1 * swap 3 4) * (swap 0 1 * swap 3 4) = 1 := by decide
  have e2 : swap (0 : Fin 5) 1 * swap 3 4 ≠ 1 := by decide
  have e3 : (swap (0 : Fin 5) 1 * swap 0 2) ^ 3 = 1 := by decide
  have e4 : swap (0 : Fin 5) 1 * swap 0 2 ≠ 1 := by decide
  have e5 : (swap (0 : Fin 5) 1 * swap 3 4) * (swap 0 1 * swap 0 2) * (swap 0 1 * swap 3 4)⁻¹ =
      (swap 0 1 * swap 0 2)⁻¹ := by decide
  refine ⟨⟨_, h1⟩, ⟨_, h2⟩, Subtype.ext e1, fun h => e2 (congrArg Subtype.val h),
    Subtype.ext (by simpa using e3), fun h => e4 (congrArg Subtype.val h), Subtype.ext ?_⟩
  simpa using e5

@[expose] def AutA5Input : Prop :=
  Function.Bijective (MulAut.conjNormal :
    Equiv.Perm (Fin 5) →* MulAut ↥(alternatingGroup (Fin 5)))

end G118

end G11

end CFSG.Quasithin
