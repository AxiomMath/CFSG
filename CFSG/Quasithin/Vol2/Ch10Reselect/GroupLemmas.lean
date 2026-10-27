module

public import CFSG.Quasithin.Background.BlueprintB2Defs
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Quasithin.Vol2.Ch10Reselect

theorem exists_pPower_lift {H Q : Type*} [Group H] [Group Q] [Finite H] (q : H →* Q) {r : ℕ}
    [Fact r.Prime] {k : H} (hk : r ∣ orderOf (q k)) :
    ∃ k' ∈ Subgroup.zpowers k, (∃ j : ℕ, orderOf k' = r ^ j) ∧ orderOf (q k') = r := by
  have hr : r.Prime := Fact.out
  obtain ⟨j, u, hru, hku⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos k).ne' r hr.ne_one
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact (orderOf_pos k).ne' (by simpa using hku)
  have hk1 : orderOf (k ^ u) = r ^ j := by
    have hdvd : u ∣ orderOf k := by rw [hku]; exact dvd_mul_left u (r ^ j)
    rw [orderOf_pow_of_dvd hu0 hdvd, hku, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hu0)]
  have hdvd1 : orderOf (q (k ^ u)) ∣ r ^ j := by
    rw [← hk1]
    exact orderOf_map_dvd q (k ^ u)
  obtain ⟨a, haj, ha⟩ := (Nat.dvd_prime_pow hr).1 hdvd1
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff, map_pow] at ha
    exact hru (hk.trans (orderOf_dvd_of_pow_eq_one ha))
  have hdvd_a : r ^ (a - 1) ∣ orderOf (q (k ^ u)) := by
    rw [ha]
    exact pow_dvd_pow r (Nat.sub_le a 1)
  have hdvd_j : r ^ (a - 1) ∣ orderOf (k ^ u) := by
    rw [hk1]
    exact pow_dvd_pow r (by omega)
  refine ⟨(k ^ u) ^ (r ^ (a - 1)), ?_, ⟨j - (a - 1), ?_⟩, ?_⟩
  · rw [← pow_mul]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers k) _
  · rw [orderOf_pow_of_dvd (pow_ne_zero _ hr.ne_zero) hdvd_j, hk1,
      Nat.pow_div (by omega) hr.pos]
  · rw [map_pow, orderOf_pow_of_dvd (pow_ne_zero _ hr.ne_zero) hdvd_a, ha,
      Nat.pow_div (Nat.sub_le a 1) hr.pos, show a - (a - 1) = 1 by omega, pow_one]

theorem le_centralizer_of_normal_of_two_power {G : Type*} [Group G] [Finite G]
    {A M N : Subgroup G} (hAM : A ≤ M)
    (hA : CFSG.Quasithin.IsPrimeReduced 2 (A.subgroupOf M)) (hNM : N ≤ M)
    (hN : (N.subgroupOf M).Normal)
    (h2 : ∀ x ∈ N, ∃ k : ℕ, x ^ (2 ^ k) ∈ Subgroup.centralizer (A : Set G)) :
    N ≤ Subgroup.centralizer (A : Set G) := by
  obtain ⟨hVnorm, -, hcore⟩ := hA
  set C : Subgroup M := Subgroup.centralizer ((A.subgroupOf M : Subgroup M) : Set M) with hC
  have hDnorm : ((N.subgroupOf M).map (QuotientGroup.mk' C)).Normal :=
    hN.map (QuotientGroup.mk' C) (QuotientGroup.mk'_surjective C)
  have hDP : IsPGroup 2 ((N.subgroupOf M).map (QuotientGroup.mk' C)) := by
    intro g
    obtain ⟨x, hx⟩ := g
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨k, hk⟩ := h2 (y : G) (Subgroup.mem_subgroupOf.mp hy)
    refine ⟨k, Subtype.ext ?_⟩
    show (QuotientGroup.mk' C y) ^ (2 ^ k) = 1
    rw [← map_pow]
    refine (QuotientGroup.eq_one_iff _).mpr ?_
    rw [hC, Subgroup.mem_centralizer_iff]
    intro a ha
    have haA : (a : G) ∈ A := Subgroup.mem_subgroupOf.mp (SetLike.mem_coe.mp ha)
    have hc := Subgroup.mem_centralizer_iff.mp hk (a : G) haA
    apply Subtype.ext
    simpa using hc
  have hDle : (N.subgroupOf M).map (QuotientGroup.mk' C) ≤ CFSG.pCore 2 (↥M ⧸ C) := by
    rw [CFSG.pCore_eq_iSup]
    exact le_iSup_of_le _ (le_iSup_of_le hDnorm (le_iSup_of_le hDP le_rfl))
  rw [hcore] at hDle
  intro x hx
  have hxM : x ∈ M := hNM hx
  have hD : QuotientGroup.mk' C (⟨x, hxM⟩ : M) ∈ (N.subgroupOf M).map (QuotientGroup.mk' C) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)
  have hone : QuotientGroup.mk' C (⟨x, hxM⟩ : M) = 1 := Subgroup.mem_bot.mp (hDle hD)
  have hxC : (⟨x, hxM⟩ : M) ∈ C := (QuotientGroup.eq_one_iff _).mp hone
  rw [hC, Subgroup.mem_centralizer_iff] at hxC
  rw [Subgroup.mem_centralizer_iff]
  intro a haA
  have haM : a ∈ M := hAM haA
  have hc := hxC ⟨a, haM⟩ (Subgroup.mem_subgroupOf.mpr haA)
  have hval := congrArg Subtype.val hc
  simpa using hval

end CFSG.Quasithin.Vol2.Ch10Reselect
