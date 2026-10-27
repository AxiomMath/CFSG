module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
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

namespace CFSG.Quasithin.H13.NQCore.L3Odd

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

theorem exists_lift_pGroup {S G : Type*} [Group S] [Group G] [Finite S] {p : ℕ} [hp : Fact p.Prime]
    (π : S →* G) (hπ : Function.Surjective π) (hker : ¬ p ∣ Nat.card π.ker)
    {P : Subgroup G} (hP : IsPGroup p P) :
    ∃ Q : Subgroup S, IsPGroup p Q ∧ Q.map π = P ∧ Disjoint Q π.ker := by
  classical
  have : Finite G := Finite.of_surjective π hπ
  set M : Subgroup S := P.comap π with hM
  obtain ⟨Q₀⟩ : Nonempty (Sylow p M) := inferInstance
  set Q : Subgroup S := (Q₀ : Subgroup M).map M.subtype with hQ
  have hQp : IsPGroup p Q := Q₀.isPGroup'.map M.subtype
  have hf : Function.Surjective ((π.comp M.subtype).codRestrict P fun x => x.2) := by
    intro y
    obtain ⟨x, hx⟩ := hπ y
    exact ⟨⟨x, by rw [hM, Subgroup.mem_comap, hx]; exact y.2⟩, Subtype.ext hx⟩
  have hR : (Q₀ : Subgroup M).map ((π.comp M.subtype).codRestrict P fun x => x.2) = ⊤ := by
    have h1 := Sylow.coe_mapSurjective hf Q₀
    rw [← h1]
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hP
    refine Subgroup.card_eq_iff_eq_top _ |>.1 ?_
    rw [Sylow.card_eq_multiplicity, hn, Nat.factorization_pow, Finsupp.smul_apply,
      Nat.Prime.factorization_self hp.out, smul_eq_mul, mul_one]
  refine ⟨Q, hQp, ?_, ?_⟩
  · have h2 : Q.map π = ((Q₀ : Subgroup M).map ((π.comp M.subtype).codRestrict P fun x => x.2)).map
        P.subtype := by
      rw [hQ, Subgroup.map_map, Subgroup.map_map]
      rfl
    rw [h2, hR, Subgroup.map_top, Subgroup.range_subtype]
  · rw [Subgroup.disjoint_def]
    intro x hxQ hxk
    obtain ⟨k, hk⟩ := hQp ⟨x, hxQ⟩
    have hk' : x ^ p ^ k = 1 := congrArg Subtype.val hk
    have h1 : orderOf x ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk'
    have h2 : orderOf x ∣ Nat.card π.ker := by
      have := Subgroup.orderOf_dvd_natCard π.ker hxk
      simpa using this
    have hcop : Nat.Coprime (p ^ k) (Nat.card π.ker) :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hker)
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

section Scalars

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem pow_three_eq_one_of_mem_scalars {x : SL(3, K)} (hx : x ∈ scalars 3 K) : x ^ 3 = 1 := by
  obtain ⟨c, hc, hxc⟩ := hx
  have h3 : ((c : K)) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  rw [hxc, ← map_pow, h3, map_one]

theorem eq_three_of_prime_dvd_card_scalars {q : ℕ} (hq : q.Prime)
    (h : q ∣ Nat.card (scalars 3 K)) : q = 3 := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := scalars 3 K) q h
  have h3 : (x : SL(3, K)) ^ 3 = 1 := pow_three_eq_one_of_mem_scalars x.2
  have h4 : orderOf (x : SL(3, K)) = q := by rw [Subgroup.orderOf_coe]; exact hx
  have h5 : q ∣ 3 := h4 ▸ orderOf_dvd_of_pow_eq_one h3
  exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 h5

theorem not_dvd_card_scalars {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) :
    ¬ p ∣ Nat.card (scalars 3 K) := fun h => hp3 (eq_three_of_prime_dvd_card_scalars hp h)

theorem not_two_dvd_card_scalars : ¬ 2 ∣ Nat.card (scalars 3 K) :=
  not_dvd_card_scalars Nat.prime_two (by norm_num)

theorem exists_lift_projectiveSL {p : ℕ} [hp : Fact p.Prime] (hp3 : p ≠ 3)
    {P : Subgroup (projectiveSL 3 K)} (hP : IsPGroup p P) :
    ∃ Q : Subgroup SL(3, K), IsPGroup p Q ∧ Q.map (proj 3 K) = P ∧ Disjoint Q (scalars 3 K) := by
  have hker : (proj 3 K).ker = scalars 3 K := QuotientGroup.ker_mk' _
  have h := exists_lift_pGroup (proj 3 K) (proj_surjective 3 K) (by
    rw [hker]
    exact not_dvd_card_scalars hp.out hp3) hP
  rwa [hker] at h

end Scalars

end CFSG.Quasithin.H13.NQCore.L3Odd
