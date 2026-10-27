module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
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
public import Mathlib.Tactic.Basify
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.RankThree.PartOne.AUTSL

theorem eq_of_sq_eq_one_of_isCyclic {C : Type*} [Group C] [Finite C] [IsCyclic C] {y z : C}
    (hy : y ^ 2 = 1) (hy1 : y ≠ 1) (hz : z ^ 2 = 1) (hz1 : z ≠ 1) : y = z := by
  classical
  have : Fintype C := Fintype.ofFinite C
  by_contra hne
  have h3 : ({1, y, z} : Finset C).card = 3 :=
    Finset.card_eq_three.2 ⟨1, y, z, hy1.symm, hz1.symm, hne, rfl⟩
  have hsub : ({1, y, z} : Finset C) ⊆ Finset.univ.filter (fun a : C => a ^ 2 = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl
    · exact one_pow 2
    · exact hy
    · exact hz
  have h1 := Finset.card_le_card hsub
  have h2 := IsCyclic.card_pow_eq_one_le (α := C) (n := 2) (by norm_num)
  omega

theorem exists_pow_mem_coset {Φ : Type*} [Group Φ] [Finite Φ] (N : Subgroup Φ) [N.Normal]
    (τ : Φ) (f : ℕ) (hgen : ∀ α : Φ, ∃ k : ℕ, (τ ^ k)⁻¹ * α ∈ N)
    (h2f : τ ^ (2 * f) ∈ N) (hf : τ ^ f ∉ N) (x : Φ) (hxN : x ∉ N) (a : ℕ)
    (hxa : x ^ 2 ^ a ∈ N) : ∃ m : ℕ, (τ ^ f)⁻¹ * x ^ m ∈ N := by
  classical
  let C := Φ ⧸ N
  have hcyc : IsCyclic C := by
    refine ⟨⟨(τ : C), fun z => ?_⟩⟩
    obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨k, hk⟩ := hgen α
    refine ⟨k, ?_⟩
    change (τ : C) ^ (k : ℤ) = (α : C)
    rw [zpow_natCast, ← QuotientGroup.mk_pow]
    exact QuotientGroup.eq.2 hk
  have hx1 : (x : C) ≠ 1 := fun h => hxN (QuotientGroup.eq_one_iff x |>.1 h)
  have hxa' : (x : C) ^ 2 ^ a = 1 := by
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).2 hxa
  have hex : ∃ b : ℕ, (x : C) ^ 2 ^ b = 1 := ⟨a, hxa'⟩
  set b := Nat.find hex with hb
  have hb1 : (x : C) ^ 2 ^ b = 1 := Nat.find_spec hex
  have hbpos : 0 < b := by
    rcases Nat.eq_zero_or_pos b with h0 | h0
    · rw [h0] at hb1
      simp only [pow_zero, pow_one] at hb1
      exact absurd hb1 hx1
    · exact h0
  have hy1 : (x : C) ^ 2 ^ (b - 1) ≠ 1 := Nat.find_min hex (by omega)
  have hy2 : ((x : C) ^ 2 ^ (b - 1)) ^ 2 = 1 := by
    rw [← pow_mul, ← pow_succ]
    have : b - 1 + 1 = b := by omega
    rw [this]
    exact hb1
  have hz2 : ((τ : C) ^ f) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, ← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).2 h2f
  have hz1 : (τ : C) ^ f ≠ 1 := fun h =>
    hf ((QuotientGroup.eq_one_iff (τ ^ f)).1 (by rw [QuotientGroup.mk_pow]; exact h))
  have heq := eq_of_sq_eq_one_of_isCyclic hy2 hy1 hz2 hz1
  refine ⟨2 ^ (b - 1), QuotientGroup.eq.1 ?_⟩
  rw [QuotientGroup.mk_pow, QuotientGroup.mk_pow]
  exact heq.symm

end CFSG.RankThree.PartOne.AUTSL
