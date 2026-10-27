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
public import Mathlib.RingTheory.PiTensorProduct
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

open scoped Matrix

namespace CFSG.ASVolI.ChH

variable {n : ℕ}

structure SubOneCover (E : Subgroup (GL (Fin n) (ZMod 2)))
    (𝒩 : Submodule (ZMod 2) (Matrix (Fin n) (Fin n) (ZMod 2))) : Prop where
  sub_one_mem : ∀ k ∈ E, ((k : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) ∈ 𝒩
  mul_mem : ∀ M ∈ 𝒩, ∀ M' ∈ 𝒩, M * M' ∈ 𝒩
  mul_comm : ∀ M ∈ 𝒩, ∀ M' ∈ 𝒩, M * M' = M' * M
  mul_self : ∀ M ∈ 𝒩, M * M = 0

@[expose] def subOneSpan (E : Subgroup (GL (Fin n) (ZMod 2))) :
    Submodule (ZMod 2) (Matrix (Fin n) (Fin n) (ZMod 2)) :=
  Submodule.span (ZMod 2) {M | ∃ k ∈ E, M = (k : Matrix (Fin n) (Fin n) (ZMod 2)) - 1}

private theorem matrix_add_self (M : Matrix (Fin n) (Fin n) (ZMod 2)) : M + M = 0 := by
  ext i j
  simp only [Matrix.add_apply, Matrix.zero_apply]
  exact (by decide : ∀ c : ZMod 2, c + c = 0) _

private theorem sub_one_mul_self_eq_zero {k : GL (Fin n) (ZMod 2)} (hk : k * k = 1) :
    ((k : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) * ((k : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) =
      0 := by
  have h1 : (k : Matrix (Fin n) (Fin n) (ZMod 2)) * k = 1 := by
    rw [← Units.val_mul, hk, Units.val_one]
  have h2 : ((k : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) * ((k : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) =
      (k : Matrix (Fin n) (Fin n) (ZMod 2)) * k - ((k : Matrix (Fin n) (Fin n) (ZMod 2)) + k) +
        1 := by
    noncomm_ring
  calc ((k : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) * ((k : Matrix (Fin n) (Fin n) (ZMod 2)) - 1)
      = 1 - ((k : Matrix (Fin n) (Fin n) (ZMod 2)) + k) + 1 := by rw [h2, h1]
    _ = (1 + 1) - ((k : Matrix (Fin n) (Fin n) (ZMod 2)) + k) := by abel
    _ = 0 := by
      rw [matrix_add_self (1 : Matrix (Fin n) (Fin n) (ZMod 2)),
        matrix_add_self (k : Matrix (Fin n) (Fin n) (ZMod 2))]
      exact sub_self _

private theorem sub_one_mul_sub_one {k l : GL (Fin n) (ZMod 2)} :
    ((k : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) * ((l : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) =
      ((↑(k * l) : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) -
        ((k : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) - ((l : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) := by
  rw [Units.val_mul]
  noncomm_ring

private theorem sub_one_mul_comm {k l : GL (Fin n) (ZMod 2)} (h : k * l = l * k) :
    ((k : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) * ((l : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) =
      ((l : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) * ((k : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) := by
  have h' : (k : Matrix (Fin n) (Fin n) (ZMod 2)) * l = l * k := by
    rw [← Units.val_mul, ← Units.val_mul, h]
  calc ((k : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) * ((l : Matrix (Fin n) (Fin n) (ZMod 2)) - 1)
      = (k : Matrix (Fin n) (Fin n) (ZMod 2)) * l - k - l + 1 := by noncomm_ring
    _ = (l : Matrix (Fin n) (Fin n) (ZMod 2)) * k - k - l + 1 := by rw [h']
    _ = ((l : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) * ((k : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) := by
      noncomm_ring

private theorem sub_one_mem_subOneSpan {E : Subgroup (GL (Fin n) (ZMod 2))}
    {k : GL (Fin n) (ZMod 2)} (hk : k ∈ E) :
    ((k : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) ∈ subOneSpan E :=
  Submodule.subset_span ⟨k, hk, rfl⟩

private theorem mul_mem_subOneSpan {E : Subgroup (GL (Fin n) (ZMod 2))}
    {M M' : Matrix (Fin n) (Fin n) (ZMod 2)} (hM : M ∈ subOneSpan E) (hM' : M' ∈ subOneSpan E) :
    M * M' ∈ subOneSpan E := by
  induction hM using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨k, hk, rfl⟩ := ha
    induction hM' using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨l, hl, rfl⟩ := hb
      rw [sub_one_mul_sub_one]
      exact Submodule.sub_mem _ (Submodule.sub_mem _ (sub_one_mem_subOneSpan (E.mul_mem hk hl))
        (sub_one_mem_subOneSpan hk)) (sub_one_mem_subOneSpan hl)
    | zero => rw [mul_zero]; exact zero_mem _
    | add b c _ _ hb hc => rw [mul_add]; exact add_mem hb hc
    | smul c b _ hb => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hb
  | zero => rw [zero_mul]; exact zero_mem _
  | add a b _ _ ha hb => rw [add_mul]; exact add_mem ha hb
  | smul c a _ ha => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ ha

private theorem mul_comm_of_mem_subOneSpan {E : Subgroup (GL (Fin n) (ZMod 2))}
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) {M M' : Matrix (Fin n) (Fin n) (ZMod 2)}
    (hM : M ∈ subOneSpan E) (hM' : M' ∈ subOneSpan E) : M * M' = M' * M := by
  induction hM using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨k, hk, rfl⟩ := ha
    induction hM' using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨l, hl, rfl⟩ := hb
      exact sub_one_mul_comm (hcomm k hk l hl)
    | zero => rw [mul_zero, zero_mul]
    | add b c _ _ hb hc => rw [mul_add, add_mul, hb, hc]
    | smul c b _ hb => rw [mul_smul_comm, smul_mul_assoc, hb]
  | zero => rw [mul_zero, zero_mul]
  | add a b _ _ ha hb => rw [add_mul, mul_add, ha, hb]
  | smul c a _ ha => rw [smul_mul_assoc, mul_smul_comm, ha]

private theorem mul_self_of_mem_subOneSpan {E : Subgroup (GL (Fin n) (ZMod 2))}
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hsq : ∀ a ∈ E, a * a = 1)
    {M : Matrix (Fin n) (Fin n) (ZMod 2)} (hM : M ∈ subOneSpan E) : M * M = 0 := by
  induction hM using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨k, hk, rfl⟩ := ha
    exact sub_one_mul_self_eq_zero (hsq k hk)
  | zero => rw [mul_zero]
  | add a b ha hb iha ihb =>
    have hab := mul_comm_of_mem_subOneSpan hcomm ha hb
    calc (a + b) * (a + b) = a * a + (a * b + b * a) + b * b := by noncomm_ring
      _ = 0 := by rw [iha, ihb, ← hab, matrix_add_self]; simp
  | smul c a ha iha => rw [smul_mul_assoc, mul_smul_comm, iha, smul_zero, smul_zero]

theorem subOneCover_subOneSpan {E : Subgroup (GL (Fin n) (ZMod 2))}
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hsq : ∀ a ∈ E, a * a = 1) :
    SubOneCover E (subOneSpan E) where
  sub_one_mem _ hk := sub_one_mem_subOneSpan hk
  mul_mem _ hM _ hM' := mul_mem_subOneSpan hM hM'
  mul_comm _ hM _ hM' := mul_comm_of_mem_subOneSpan hcomm hM hM'
  mul_self _ hM := mul_self_of_mem_subOneSpan hcomm hsq hM

end CFSG.ASVolI.ChH
