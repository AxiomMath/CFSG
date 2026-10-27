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
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
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

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T517

variable {N ι : Type*} [Group N]

@[expose] def coordSub (N : Type*) [Group N] (ι : Type*) (k : ι) : Subgroup (ι → N) where
  carrier := {y | ∀ k', k' ≠ k → y k' = 1}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun {a b} ha hb k' hk' => by simp [ha k' hk', hb k' hk']
  inv_mem' := fun {a} ha k' hk' => by simp [ha k' hk']

theorem mem_coordSub {k : ι} {y : ι → N} : y ∈ coordSub N ι k ↔ ∀ k', k' ≠ k → y k' = 1 :=
  Iff.rfl

instance (k : ι) : (coordSub N ι k).Normal :=
  ⟨fun y hy g k' hk' => by simp [hy k' hk']⟩

theorem exists_le_coordSub [DecidableEq ι] (hN : Subgroup.center N = ⊥)
    {M : Subgroup (ι → N)} [M.Normal] [IsSimpleGroup M] : ∃ k : ι, M ≤ coordSub N ι k := by
  by_contra hcon
  push Not at hcon
  have hbot : ∀ k : ι, (coordSub N ι k).subgroupOf M = ⊥ := by
    intro k
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((coordSub N ι k).subgroupOf M) with h | h
    · exact h
    · exact absurd (Subgroup.subgroupOf_eq_top.mp h) (hcon k)
  have hone : ∀ y ∈ M, y = 1 := by
    intro y hy
    funext k
    have hcomm : ∀ a : N, y k * a = a * y k := by
      intro a
      have hy'mem : (Pi.mulSingle k a : ι → N) ∈ coordSub N ι k := fun k' hk' => by
        simp [hk']
      have h1 : y * Pi.mulSingle k a * y⁻¹ * (Pi.mulSingle k a)⁻¹ ∈ coordSub N ι k := by
        have := (inferInstance : (coordSub N ι k).Normal).conj_mem _ hy'mem y
        exact mul_mem this (inv_mem hy'mem)
      have h2 : y * Pi.mulSingle k a * y⁻¹ * (Pi.mulSingle k a)⁻¹ ∈ M := by
        have hyM : Pi.mulSingle k a * y⁻¹ * (Pi.mulSingle k a)⁻¹ ∈ M := by
          have := (inferInstance : M.Normal).conj_mem y⁻¹ (inv_mem hy) (Pi.mulSingle k a)
          simpa [mul_assoc] using this
        simpa [mul_assoc] using mul_mem hy hyM
      have h3 : (⟨y * Pi.mulSingle k a * y⁻¹ * (Pi.mulSingle k a)⁻¹, h2⟩ : M) ∈
          (coordSub N ι k).subgroupOf M := h1
      rw [hbot k, Subgroup.mem_bot] at h3
      have h4 : y * Pi.mulSingle k a * y⁻¹ * (Pi.mulSingle k a)⁻¹ = 1 := congrArg Subtype.val h3
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h4
      have := congrFun h4 k
      simpa using this
    have hk : y k ∈ Subgroup.center N := by
      rw [Subgroup.mem_center_iff]
      exact fun a => (hcomm a).symm
    rw [hN, Subgroup.mem_bot] at hk
    simpa using hk
  have : (⊤ : Subgroup M) = ⊥ := by
    rw [eq_bot_iff]
    intro x _
    exact Subgroup.mem_bot.mpr (Subtype.ext (hone x x.2))
  exact (Subgroup.nontrivial_iff_ne_bot ⊤).mp inferInstance this

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T517
