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

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup Pointwise

theorem s16t3_exists_permuting_three_of_two_three {A Q : Type*} [Group A] [Finite A] [Group Q]
    (φ : A →* Q) {T : Subgroup A} (hT2 : IsPGroup 2 ↥T) (hTsyl : ¬ 2 ∣ T.index)
    {J : Subgroup Q} (hTJ : T.map φ ≤ J) {x y : ℕ}
    (hJA : Nat.card ↥(J.comap φ) = 2 ^ x * 3 ^ y) :
    ∃ Y : Subgroup A, IsPGroup 3 ↥Y ∧ Nat.card ↥Y = 3 ^ y ∧
      (Y : Set A) * (T : Set A) = (T : Set A) * (Y : Set A) ∧ Y ≤ J.comap φ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set JA : Subgroup A := J.comap φ
  have hTJA : T ≤ JA := Subgroup.map_le_iff_le_comap.mp hTJ
  obtain ⟨b, hb⟩ := hT2.exists_card_eq
  have hrel : ¬ 2 ∣ T.relIndex JA := fun h => hTsyl (h.trans
    (Subgroup.relIndex_dvd_index_of_le hTJA))
  have hTJcard : Nat.card ↥T * T.relIndex JA = Nat.card ↥JA := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTJA).toEquiv]
    exact (T.subgroupOf JA).card_mul_index
  have hbx : b = x := by
    have h := congrArg (fun n => Nat.factorization n 2) (hTJcard.trans hJA)
    have hr0 : T.relIndex JA ≠ 0 := fun h0 => hrel (h0 ▸ dvd_zero 2)
    simp only [hb] at h
    rw [Nat.factorization_mul (by positivity) hr0, Nat.factorization_mul (by positivity)
      (by positivity), Finsupp.add_apply, Finsupp.add_apply, Nat.factorization_pow,
      Nat.factorization_pow, Nat.factorization_pow] at h
    simp [Nat.factorization_eq_zero_of_not_dvd hrel, Nat.Prime.factorization_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3)] at h
    exact h
  let P : Sylow 3 ↥JA := Classical.arbitrary _
  have hfac : Nat.factorization (Nat.card ↥JA) 3 = y := by
    rw [hJA, Nat.factorization_mul (by positivity) (by positivity), Finsupp.add_apply,
      Nat.factorization_pow, Nat.factorization_pow, Finsupp.smul_apply, Finsupp.smul_apply,
      Nat.Prime.factorization_self Nat.prime_three,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 2)]
    simp
  have hPcard : Nat.card ↥P = 3 ^ y := by
    change Nat.card ↥(P : Subgroup ↥JA) = 3 ^ y
    rw [P.card_eq_multiplicity, hfac]
  let Y : Subgroup A := (P : Subgroup ↥JA).map JA.subtype
  have hYle : Y ≤ JA := Subgroup.map_subtype_le (H := JA) P
  have hYcard : Nat.card ↥Y = 3 ^ y := (Subgroup.card_subtype JA P).trans hPcard
  have hYcard' : Nat.card ↥(Y.subgroupOf JA) = 3 ^ y := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYle).toEquiv, hYcard]
  have hTcard' : Nat.card ↥(T.subgroupOf JA) = 2 ^ x := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTJA).toEquiv, hb, hbx]
  have hprod : Nat.card ↥(Y.subgroupOf JA) * Nat.card ↥(T.subgroupOf JA) = Nat.card ↥JA := by
    rw [hYcard', hTcard', hJA, mul_comm]
  have hcop : Nat.Coprime (Nat.card ↥(Y.subgroupOf JA)) (Nat.card ↥(T.subgroupOf JA)) := by
    rw [hYcard', hTcard']
    exact Nat.coprime_pow_primes y x Nat.prime_three Nat.prime_two (by norm_num)
  have hcompl : Subgroup.IsComplement' (Y.subgroupOf JA) (T.subgroupOf JA) :=
    Subgroup.isComplement'_of_coprime hprod hcop
  refine ⟨Y, P.isPGroup'.map JA.subtype, hYcard, ?_, hYle⟩
  have himgY : JA.subtype '' (Y.subgroupOf JA : Set ↥JA) = (Y : Set A) := by
    rw [← Subgroup.coe_map, Subgroup.map_subgroupOf_eq_of_le hYle]
  have himgT : JA.subtype '' (T.subgroupOf JA : Set ↥JA) = (T : Set A) := by
    rw [← Subgroup.coe_map, Subgroup.map_subgroupOf_eq_of_le hTJA]
  have himgu : JA.subtype '' (Set.univ : Set ↥JA) = (JA : Set A) := by
    rw [Set.image_univ, ← MonoidHom.coe_range, Subgroup.range_subtype]
  have hYT : (Y : Set A) * (T : Set A) = (JA : Set A) := by
    have h := congrArg (Set.image JA.subtype) hcompl.mul_eq
    rw [Set.image_mul JA.subtype, himgY, himgT, himgu] at h
    exact h
  have hTY : (T : Set A) * (Y : Set A) = (JA : Set A) := by
    have h := congrArg (Set.image JA.subtype) hcompl.symm.mul_eq
    rw [Set.image_mul JA.subtype, himgT, himgY, himgu] at h
    exact h
  exact hYT.trans hTY.symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
