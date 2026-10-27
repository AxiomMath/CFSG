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
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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

public section

namespace CFSG.Quasithin.Vol2.Ch10Reselect

open Matrix

private lemma cardGL_two_eq (K : Type*) [Field K] [Finite K] :
    Nat.card (GL (Fin 2) K) = (Nat.card K ^ 2 - 1) * (Nat.card K ^ 2 - Nat.card K) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  rw [Matrix.card_GL_field, Fin.prod_univ_two, Nat.card_eq_fintype_card]
  simp

private lemma cardSL_mul_two (K : Type*) [Field K] [Finite K] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) * (Nat.card K - 1) =
      Nat.card (GL (Fin 2) K) := by
  rw [← Nat.card_units K]
  exact Matrix.card_SL_mul_card_units

theorem card_SL_two (K : Type*) [Field K] [Finite K] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) = Nat.card K * (Nat.card K ^ 2 - 1) := by
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hmul := cardSL_mul_two K
  rw [cardGL_two_eq K] at hmul
  have hsub : Nat.card K ^ 2 - Nat.card K = Nat.card K * (Nat.card K - 1) := by
    rw [Nat.mul_sub_one, sq]
  rw [hsub] at hmul
  apply Nat.eq_of_mul_eq_mul_right (show 0 < Nat.card K - 1 by omega)
  rw [hmul]
  ring

theorem card_GL_two (K : Type*) [Field K] [Finite K] :
    Nat.card (GL (Fin 2) K) = (Nat.card K - 1) * Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) := by
  rw [← cardSL_mul_two K]
  ring

theorem not_dvd_card_GL_two_of_not_dvd_card_SL_two {K : Type*} [Field K] [Finite K] {r : ℕ}
    (hr : r.Prime) (h : ¬ r ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) K)) :
    ¬ r ∣ Nat.card (GL (Fin 2) K) := by
  rw [card_SL_two K] at h
  rw [card_GL_two K, card_SL_two K]
  intro hdvd
  rcases (Nat.Prime.dvd_mul hr).mp hdvd with h1 | h1
  · have h2 : Nat.card K - 1 ∣ Nat.card K ^ 2 - 1 := by
      have := Nat.sub_dvd_pow_sub_pow (Nat.card K) 1 2
      rwa [one_pow] at this
    exact h (Dvd.dvd.mul_left (h1.trans h2) _)
  · exact h h1

theorem scalar_of_pow_eq_one_of_coprime {K : Type*} [Field K] [Finite K] (B : GL (Fin 2) K)
    {m : ℕ} (hm : B ^ m = 1) (hcop : Nat.Coprime m (Nat.card K * (Nat.card K ^ 2 - 1))) :
    ∃ c : K, (B : Matrix (Fin 2) (Fin 2) K) = Matrix.scalar (Fin 2) c := by
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hinj : Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin 2) : Kˣ →* GL (Fin 2) K) := by
    intro a b h
    exact Units.ext ((Matrix.scalar (Fin 2)).injective
      (by simpa using congrArg (fun M : GL (Fin 2) K => (M : Matrix (Fin 2) (Fin 2) K)) h))
  have hZ : Nat.card (Subgroup.center (GL (Fin 2) K)) = Nat.card K - 1 := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar, ← Nat.card_units K]
    exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
  have hindex : (Subgroup.center (GL (Fin 2) K)).index = Nat.card K * (Nat.card K ^ 2 - 1) := by
    have h1 := Subgroup.card_mul_index (Subgroup.center (GL (Fin 2) K))
    rw [hZ, card_GL_two K, card_SL_two K] at h1
    exact Nat.eq_of_mul_eq_mul_left (show 0 < Nat.card K - 1 by omega) h1
  have hpow : (QuotientGroup.mk' (Subgroup.center (GL (Fin 2) K)) B) ^ m = 1 := by
    rw [← map_pow, hm, map_one]
  have hd1 : orderOf (QuotientGroup.mk' (Subgroup.center (GL (Fin 2) K)) B) ∣ m :=
    orderOf_dvd_of_pow_eq_one hpow
  have hd2 : orderOf (QuotientGroup.mk' (Subgroup.center (GL (Fin 2) K)) B) ∣
      Nat.card K * (Nat.card K ^ 2 - 1) := by
    rw [← hindex, Subgroup.index_eq_card]
    exact orderOf_dvd_natCard _
  have hone : orderOf (QuotientGroup.mk' (Subgroup.center (GL (Fin 2) K)) B) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hd1 hcop) hd2
  have hB1 : QuotientGroup.mk' (Subgroup.center (GL (Fin 2) K)) B = 1 :=
    orderOf_eq_one_iff.mp hone
  have hBZ : B ∈ Subgroup.center (GL (Fin 2) K) :=
    (QuotientGroup.eq_one_iff (N := Subgroup.center (GL (Fin 2) K)) B).mp hB1
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hBZ
  obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp hBZ
  exact ⟨(u : K), (congrArg (fun M : GL (Fin 2) K => (M : Matrix (Fin 2) (Fin 2) K)) hu).symm⟩

end CFSG.Quasithin.Vol2.Ch10Reselect
