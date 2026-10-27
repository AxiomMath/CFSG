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
public import Mathlib.RingTheory.SimpleRing.Principal
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

namespace CFSG.Quasithin.OrthMinus

variable {K : Type} [Field K] [CharP K 2]

@[expose] def sg (K : Type) [Field K] [CharP K 2] (a : ℕ) : K →+* K := iterateFrobenius K 2 a

theorem sg_apply (a : ℕ) (x : K) : sg K a x = x ^ 2 ^ a := iterateFrobenius_def 2 a x

theorem sg_sg [Finite K] {a : ℕ} (hK : Nat.card K = 2 ^ (2 * a)) (x : K) :
    sg K a (sg K a x) = x := by
  have := Fintype.ofFinite K
  have hc : Fintype.card K = 2 ^ (2 * a) := by rw [← hK, Nat.card_eq_fintype_card]
  rw [sg_apply, sg_apply, ← pow_mul, ← pow_add, ← two_mul, ← hc, FiniteField.pow_card]

theorem add_eq_zero_iff_eq (x y : K) : x + y = 0 ↔ x = y := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    linear_combination h - y * h2
  · rw [h]
    exact CharTwo.add_self_eq_zero y

theorem card_fixed_le [Finite K] {a : ℕ} (ha : 1 ≤ a) :
    Nat.card {x : K // sg K a x = x} ≤ 2 ^ a := by
  classical
  have := Fintype.ofFinite K
  set p : Polynomial K := Polynomial.X ^ 2 ^ a - Polynomial.X with hp
  have hdeg : p.natDegree = 2 ^ a :=
    FiniteField.X_pow_card_pow_sub_X_natDegree_eq K (by omega) (by norm_num)
  have hne : p ≠ 0 := FiniteField.X_pow_card_pow_sub_X_ne_zero K (by omega) (by norm_num)
  have hsub : (Finset.univ.filter fun x : K => sg K a x = x).val ⊆ p.roots := by
    intro x hx
    have hx' : sg K a x = x := (Finset.mem_filter.mp hx).2
    rw [Polynomial.mem_roots hne, Polynomial.IsRoot, hp, Polynomial.eval_sub,
      Polynomial.eval_pow, Polynomial.eval_X, ← sg_apply, hx', sub_self]
  have h := Polynomial.card_le_degree_of_subset_roots hsub
  rw [hdeg] at h
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact h

@[expose] def trc (a : ℕ) : K →+ K := AddMonoidHom.id K + (sg K a).toAddMonoidHom

theorem trc_apply (a : ℕ) (x : K) : trc a x = x + sg K a x := rfl

theorem card_le_card_fixed_sq [Finite K] {a : ℕ} (hK : Nat.card K = 2 ^ (2 * a)) :
    Nat.card K ≤ Nat.card {x : K // sg K a x = x} ^ 2 := by
  have hsg := sg_sg hK
  have h1 := AddSubgroup.card_ker_mul_card_range (trc (K := K) a)
  have hker : Nat.card (trc (K := K) a).ker = Nat.card {x : K // sg K a x = x} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    rw [AddMonoidHom.mem_ker, trc_apply, add_eq_zero_iff_eq]
    exact eq_comm
  have hrange : Nat.card (trc (K := K) a).range ≤ Nat.card {x : K // sg K a x = x} := by
    have : Finite {x : K // sg K a x = x} := inferInstance
    refine Nat.card_le_card_of_injective
      (fun y => (⟨(y : K), ?_⟩ : {x : K // sg K a x = x})) ?_
    · obtain ⟨y, x, rfl⟩ := y
      change sg K a (trc a x) = trc a x
      rw [trc_apply, map_add, hsg, add_comm]
    · intro y z h
      have h' := congrArg Subtype.val h
      exact Subtype.ext h'
  rw [← h1, hker, sq]
  exact Nat.mul_le_mul_left _ hrange

theorem card_fixed [Finite K] {a : ℕ} (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a)) :
    Nat.card {x : K // sg K a x = x} = 2 ^ a := by
  have h1 := card_fixed_le (K := K) ha
  have h2 := card_le_card_fixed_sq (K := K) hK
  have h3 : (2 : ℕ) ^ (2 * a) = (2 ^ a) ^ 2 := by rw [← pow_mul, mul_comm]
  rw [hK, h3] at h2
  exact le_antisymm h1 ((Nat.pow_le_pow_iff_left two_ne_zero).mp h2)

end CFSG.Quasithin.OrthMinus
