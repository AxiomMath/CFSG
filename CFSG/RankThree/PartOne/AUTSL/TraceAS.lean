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

namespace CFSG.RankThree.PartOne.AUTSL

section TraceAS

variable {K : Type} [Field K] [Fintype K] [CharP K 2]

omit [Fintype K] in
theorem sum_pow_sq_add (m : ℕ) (y : K) :
    ∑ i ∈ Finset.range m, (y * y) ^ (2 ^ i) + ∑ i ∈ Finset.range m, y ^ (2 ^ i) =
      y ^ (2 ^ m) + y := by
  induction m with
  | zero => simp [CharTwo.add_self_eq_zero]
  | succ m ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have h1 : (y * y) ^ (2 ^ m) = y ^ (2 ^ (m + 1)) := by
      rw [← sq, ← pow_mul, pow_succ, mul_comm]
    have h2 : y ^ (2 ^ m) + y ^ (2 ^ m) = 0 := CharTwo.add_self_eq_zero _
    linear_combination ih + h1 + h2

omit [Fintype K] in
theorem sum_pow_add (m : ℕ) (x y : K) :
    ∑ i ∈ Finset.range m, (x + y) ^ (2 ^ i) =
      ∑ i ∈ Finset.range m, x ^ (2 ^ i) + ∑ i ∈ Finset.range m, y ^ (2 ^ i) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact add_pow_char_pow x y 2 i

def sumPowHom (m : ℕ) : K →+ K where
  toFun y := ∑ i ∈ Finset.range m, y ^ (2 ^ i)
  map_zero' := Finset.sum_eq_zero fun i _ => zero_pow (pow_ne_zero i two_ne_zero)
  map_add' x y := sum_pow_add m x y

def artinSchreierHom : K →+ K where
  toFun y := y * y + y
  map_zero' := by simp
  map_add' x y := by
    have : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination (x * y) * this

theorem artinSchreierHom_range_index :
    (artinSchreierHom (K := K)).range.index = 2 := by
  have hker : ∀ x : K, x ∈ (artinSchreierHom (K := K)).ker ↔ x ∈ ({0, 1} : Set K) := fun x => by
    rw [AddMonoidHom.mem_ker, Set.mem_insert_iff, Set.mem_singleton_iff]
    change x * x + x = 0 ↔ _
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have : x * x + x = x * (x - 1) := by linear_combination (x : K) * h2
    rw [this, mul_eq_zero, sub_eq_zero]
  have hcard : Nat.card (artinSchreierHom (K := K)).ker = 2 := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight hker), Nat.card_coe_set_eq,
      Set.ncard_pair zero_ne_one]
  have h1 := AddSubgroup.card_ker_mul_card_range (artinSchreierHom (K := K))
  have h2 := AddSubgroup.card_mul_index (artinSchreierHom (K := K)).range
  rw [hcard] at h1
  have hpos : 0 < Nat.card (artinSchreierHom (K := K)).range := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hpos (by rw [h2, ← h1, mul_comm])

theorem exists_sq_add_eq_of_trace_zero {f : ℕ} (hf : Fintype.card K = 2 ^ f) (γ : K)
    (hγ : ∑ i ∈ Finset.range f, γ ^ (2 ^ i) = 0) : ∃ y : K, y * y + y = γ := by
  classical
  have hs_ne : ∃ y : K, ∑ i ∈ Finset.range f, y ^ (2 ^ i) ≠ 0 := by
    let _ : Algebra (ZMod 2) K := ZMod.algebra K 2
    have hsep : Algebra.IsSeparable (ZMod 2) K := inferInstance
    have hfd : FiniteDimensional (ZMod 2) K := inferInstance
    obtain ⟨y, hy⟩ : ∃ y, Algebra.trace (ZMod 2) K y ≠ 0 := by
      by_contra h
      push Not at h
      exact Algebra.trace_ne_zero (ZMod 2) K (LinearMap.ext fun y => h y)
    refine ⟨y, ?_⟩
    have h1 := FiniteField.algebraMap_trace_eq_sum_pow (ZMod 2) K y
    have hrank : Module.finrank (ZMod 2) K = f := by
      have := Module.card_eq_pow_finrank (K := ZMod 2) (V := K)
      rw [hf, ZMod.card] at this
      exact (Nat.pow_right_injective (le_refl 2) this).symm
    rw [hrank, Nat.card_zmod] at h1
    rw [← h1]
    exact (map_ne_zero (algebraMap (ZMod 2) K)).2 hy
  obtain ⟨y₀, hy₀⟩ := hs_ne
  have hle : (artinSchreierHom (K := K)).range ≤ (sumPowHom (K := K) f).ker := by
    rintro _ ⟨y, rfl⟩
    rw [AddMonoidHom.mem_ker]
    change ∑ i ∈ Finset.range f, (y * y + y) ^ (2 ^ i) = 0
    rw [sum_pow_add]
    have h := sum_pow_sq_add f y
    have hy : y ^ (2 ^ f) = y := by
      rw [← hf]
      exact FiniteField.pow_card y
    rw [hy] at h
    rw [h]
    exact CharTwo.add_self_eq_zero y
  have hker_ne : (sumPowHom (K := K) f).ker ≠ ⊤ := by
    intro htop
    have : y₀ ∈ (sumPowHom (K := K) f).ker := htop ▸ AddSubgroup.mem_top y₀
    exact hy₀ this
  have hdvd := AddSubgroup.index_dvd_of_le hle
  rw [artinSchreierHom_range_index] at hdvd
  have hne1 : (sumPowHom (K := K) f).ker.index ≠ 1 := by
    intro h
    exact hker_ne (AddSubgroup.index_eq_one.1 h)
  have hidx2 : (sumPowHom (K := K) f).ker.index = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact absurd h hne1
    · exact h
  have hcard : Nat.card (sumPowHom (K := K) f).ker =
      Nat.card (artinSchreierHom (K := K)).range := by
    have h1 := AddSubgroup.card_mul_index (sumPowHom (K := K) f).ker
    have h2 := AddSubgroup.card_mul_index (artinSchreierHom (K := K)).range
    rw [hidx2] at h1
    rw [artinSchreierHom_range_index] at h2
    omega
  have hEq : (artinSchreierHom (K := K)).range = (sumPowHom (K := K) f).ker :=
    AddSubgroup.eq_of_le_of_card_ge hle (le_of_eq hcard)
  have hγmem : γ ∈ (sumPowHom (K := K) f).ker := by
    rw [AddMonoidHom.mem_ker]
    exact hγ
  rw [← hEq] at hγmem
  obtain ⟨y, hy⟩ := hγmem
  exact ⟨y, hy⟩

end TraceAS

end CFSG.RankThree.PartOne.AUTSL
