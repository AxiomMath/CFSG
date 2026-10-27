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
public import Mathlib.GroupTheory.SchurZassenhaus
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

namespace CFSG.Quasithin.RonanE611

variable {G : Type} [Group G] [Finite G]

theorem exists_cyclic_of_exponent {A : Type*} [Group A] {B : Subgroup G} (φ : ↥B →* A)
    (hcyc : IsCyclic ↥φ.range) (hodd : Odd (Nat.card ↥φ.range))
    (hexp : ∀ g : ↥B, ∃ k : ℕ, (g ^ Nat.card ↥φ.range) ^ (2 ^ k) = 1) :
    ∃ X : Subgroup G, X ≤ B ∧ IsCyclic ↥X ∧ Nat.card ↥X = Nat.card ↥φ.range ∧
      ∀ a ∈ φ.range, ∃ x : ↥B, (x : G) ∈ X ∧ φ x = a := by
  classical
  haveI : Finite ↥φ.range := Finite.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  obtain ⟨ξ, hξ⟩ := hcyc.exists_generator
  obtain ⟨b, hb⟩ : ∃ b : ↥B, φ b = (ξ : A) := ξ.2
  set d := Nat.card ↥φ.range with hd
  have hdpos : 0 < d := Nat.card_pos
  have hordξ : orderOf ξ = d := orderOf_eq_card_of_forall_mem_zpowers hξ
  have hordξA : orderOf (ξ : A) = d := by rw [Subgroup.orderOf_coe, hordξ]
  have hordφ : orderOf (φ b) = d := by rw [hb, hordξA]
  have hdm : d ∣ orderOf b := by
    rw [← hordφ]
    exact orderOf_map_dvd φ b
  obtain ⟨k, hk⟩ := hexp b
  have hm : orderOf b ∣ d * 2 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    rw [pow_mul]
    exact hk
  obtain ⟨e, he⟩ := hdm
  have hed : e ∣ 2 ^ k := by
    have h1 : d * e ∣ d * 2 ^ k := by rw [← he]; exact hm
    exact Nat.dvd_of_mul_dvd_mul_left hdpos h1
  obtain ⟨a, -, hea⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hed
  have hordb : orderOf b = d * 2 ^ a := by rw [he, hea]
  set b' : ↥B := b ^ 2 ^ a with hb'
  have hordb' : orderOf b' = d := by
    rw [hb', orderOf_pow' _ (by positivity : 2 ^ a ≠ 0), hordb]
    have : Nat.gcd (d * 2 ^ a) (2 ^ a) = 2 ^ a := Nat.gcd_eq_right (Dvd.intro_left _ rfl)
    rw [this]
    exact Nat.mul_div_cancel _ (by positivity)
  have hcop : Nat.Coprime (2 ^ a) d := by
    refine Nat.Coprime.pow_left a ?_
    exact hodd.coprime_two_left
  refine ⟨Subgroup.zpowers ((b' : ↥B) : G), ?_, inferInstance, ?_, ?_⟩
  · rw [Subgroup.zpowers_le]
    exact b'.2
  · rw [Nat.card_zpowers, Subgroup.orderOf_coe, hordb']
  · intro y hy
    obtain ⟨i, hi⟩ := hξ ⟨y, hy⟩
    have hi' : (ξ : A) ^ i = y := congrArg Subtype.val hi
    obtain ⟨u, v, huv⟩ : IsCoprime ((2 : ℤ) ^ a) (d : ℤ) := by
      have := Nat.isCoprime_iff_coprime.2 hcop
      exact_mod_cast this
    refine ⟨b' ^ (i * u), ?_, ?_⟩
    · rw [Subgroup.coe_zpow]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _
    · rw [map_zpow, hb', map_pow, hb, ← hi', ← zpow_natCast, ← zpow_mul]
      have h1 : ((2 : ℤ) ^ a * (i * u)) = i - (i * v) * (d : ℤ) := by
        linear_combination (i : ℤ) * huv
      have h2 : (((2 ^ a : ℕ) : ℤ)) * (i * u) = i - (i * v) * (d : ℤ) := by
        push_cast; exact h1
      have h3 : (ξ : A) ^ (d : ℤ) = 1 := by
        rw [zpow_natCast, ← hordξA]
        exact pow_orderOf_eq_one _
      rw [h2, zpow_sub, zpow_mul', h3, one_zpow, inv_one, mul_one]

theorem exists_complement_of_coprime {A : Type*} [Group A] {B : Subgroup G} (φ : ↥B →* A)
    (hcyc : IsCyclic ↥φ.range)
    (hcop : Nat.Coprime (Nat.card ↥φ.ker) (Nat.card ↥φ.range)) :
    ∃ X : Subgroup G, X ≤ B ∧ IsCyclic ↥X ∧ Nat.card ↥X = Nat.card ↥φ.range ∧
      ∀ a ∈ φ.range, ∃ x : ↥B, (x : G) ∈ X ∧ φ x = a := by
  classical
  haveI : Finite ↥φ.range := Finite.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hidx : φ.ker.index = Nat.card ↥φ.range := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
    rfl
  obtain ⟨H, hH⟩ := Subgroup.exists_right_complement'_of_coprime (N := φ.ker)
    (by rw [hidx]; exact hcop)
  have hcard : Nat.card ↥φ.ker * Nat.card ↥H = Nat.card ↥B := hH.card_mul
  have hdisj : Disjoint φ.ker H := hH.disjoint
  have hker : Nat.card ↥φ.ker * Nat.card ↥φ.range = Nat.card ↥B := by
    rw [← hidx, mul_comm]
    exact Subgroup.index_mul_card φ.ker
  have hHcard : Nat.card ↥H = Nat.card ↥φ.range := by
    have hpos : 0 < Nat.card ↥φ.ker := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (hcard.trans hker.symm)
  let ψ : ↥H →* ↥φ.range := φ.rangeRestrict.comp H.subtype
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro h hh
    have h1 : φ (h : ↥B) = 1 := by
      have := congrArg Subtype.val hh
      simpa [ψ] using this
    have h2 : (h : ↥B) ∈ φ.ker := h1
    have h3 : (h : ↥B) ∈ φ.ker ⊓ H := ⟨h2, h.2⟩
    rw [disjoint_iff.1 hdisj, Subgroup.mem_bot] at h3
    exact Subtype.ext h3
  have hψbij : Function.Bijective ψ :=
    (Function.Injective.bijective_of_nat_card_le hψinj (by rw [hHcard]))
  refine ⟨H.map B.subtype, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  · have : IsCyclic ↥H := isCyclic_of_injective ψ hψinj
    exact (isCyclic_of_surjective (H.equivMapOfInjective B.subtype B.subtype_injective).toMonoidHom
      (H.equivMapOfInjective B.subtype B.subtype_injective).surjective)
  · rw [Subgroup.card_map_of_injective B.subtype_injective, hHcard]
  · intro a ha
    obtain ⟨h, hh⟩ := hψbij.2 ⟨a, ha⟩
    refine ⟨(h : ↥B), ⟨(h : ↥B), h.2, rfl⟩, ?_⟩
    exact congrArg Subtype.val hh

end CFSG.Quasithin.RonanE611
