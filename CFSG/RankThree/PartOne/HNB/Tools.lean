module

public import CFSG.Adapters.QiuzhenLegacy.GorensteinWalter.Section2.CoprimeTools
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Monotonicity.Lemmas
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

namespace CFSG.RankThree.PartOne.HNB

open Subgroup CFSG
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem zpowers_le_centralizer_zpowers {a b : G} (h : a * b = b * a) :
    Subgroup.zpowers a ≤ Subgroup.centralizer (Subgroup.zpowers b : Set G) := by
  rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
  intro g hg
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  exact (Commute.zpow_left (show Commute b a from h.symm) n).eq

theorem mem_normalizer_zpowers_of_commute {a t : G} (h : a * t = t * a) :
    a ∈ Subgroup.normalizer ((Subgroup.zpowers t : Subgroup G) : Set G) := by
  have hconj : ∀ m ∈ Subgroup.zpowers t, a * m * a⁻¹ = m := by
    intro m hm
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hm
    have h1 : a * t ^ n = t ^ n * a := (Commute.zpow_right (show Commute a t from h) n).eq
    rw [h1, mul_assoc, mul_inv_cancel, mul_one]
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    rw [hconj g hg]
    exact hg
  · intro hg
    have h2 := hconj _ hg
    have h3 : a * g * a⁻¹ = g := by
      have := congrArg (fun z => a⁻¹ * z * a) h2
      simpa [mul_assoc] using this
    rw [← h3]
    exact hg

theorem mem_normalizer_centralizer_of_commute {a b : G} (h : a * b = b * a) :
    a ∈ Subgroup.normalizer ((Subgroup.centralizer ({b} : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  have hb : a⁻¹ * b = b * a⁻¹ := by
    calc a⁻¹ * b = a⁻¹ * (b * a) * a⁻¹ := by group
      _ = a⁻¹ * (a * b) * a⁻¹ := by rw [h]
      _ = b * a⁻¹ := by group
  have e1 : (a * g * a⁻¹) * b = a * (g * b) * a⁻¹ := by
    calc (a * g * a⁻¹) * b = a * g * (a⁻¹ * b) := by group
      _ = a * g * (b * a⁻¹) := by rw [hb]
      _ = a * (g * b) * a⁻¹ := by group
  have e2 : b * (a * g * a⁻¹) = a * (b * g) * a⁻¹ := by
    calc b * (a * g * a⁻¹) = (b * a) * g * a⁻¹ := by group
      _ = (a * b) * g * a⁻¹ := by rw [h]
      _ = a * (b * g) * a⁻¹ := by group
  rw [e1, e2]
  constructor
  · intro hh
    rw [hh]
  · intro hh
    exact mul_left_cancel (mul_right_cancel hh)

theorem commutator_zpowers_eq_bot_iff {U : Subgroup G} {c : G} :
    ⁅U, Subgroup.zpowers c⁆ = ⊥ ↔ ∀ u ∈ U, u * c = c * u := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  constructor
  · intro h u hu
    have := Subgroup.mem_centralizer_iff.mp (h hu) c (Subgroup.mem_zpowers c)
    exact this.symm
  · intro h u hu
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact ((Commute.zpow_left (show Commute c u from (h u hu).symm) n).symm).eq.symm ▸ rfl

open CFSG in
theorem commutator_double_eq_self_of_coprime_solvable [Finite G] (P K : Subgroup G)
    (hPK : P ≤ Subgroup.normalizer (K : Set G))
    (hcop : Nat.Coprime (Nat.card P) (Nat.card (↥K))) (hsolv : Group.IsSolvable K) :
    ⁅⁅K, P⁆, P⁆ = ⁅K, P⁆ :=
  GL83.commutator_double_eq_self P K hPK hcop hsolv

theorem coprime_five_card_of_isPGroup_two [Finite G] {S : Subgroup G} (hS : IsPGroup 2 S) :
    Nat.Coprime 5 (Nat.card S) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS
  rw [hk]
  exact Nat.Coprime.pow_right _ (by norm_num)

theorem commutator_zpowers_self [Finite G] {c : G} (hc5 : orderOf c = 5) {S : Subgroup G}
    (hS2 : IsPGroup 2 S) (hcS : c ∈ Subgroup.normalizer (S : Set G)) :
    ⁅⁅S, Subgroup.zpowers c⁆, Subgroup.zpowers c⁆ = ⁅S, Subgroup.zpowers c⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers c)) (Nat.card S) := by
    rw [Nat.card_zpowers, hc5]
    exact coprime_five_card_of_isPGroup_two hS2
  have : Group.IsNilpotent S := hS2.isNilpotent
  exact commutator_double_eq_self_of_coprime_solvable (Subgroup.zpowers c) S
    (Subgroup.zpowers_le.mpr hcS) hcop inferInstance

theorem mem_zpowers_of_mem_zpowers_prime [Finite G] {p : ℕ} [Fact p.Prime] {g h : G}
    (hh : orderOf h = p) (hgh : g ∈ Subgroup.zpowers h) (hg1 : g ≠ 1) :
    h ∈ Subgroup.zpowers g := by
  have hle := Subgroup.zpowers_le.mpr hgh
  have hdvd : orderOf g ∣ p := hh ▸ orderOf_dvd_of_mem_zpowers hgh
  have hg : orderOf g = p :=
    ((Nat.dvd_prime (Fact.out : p.Prime)).mp hdvd).resolve_left fun h1 =>
      hg1 (orderOf_eq_one_iff.mp h1)
  have heq : Subgroup.zpowers g = Subgroup.zpowers h :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hh, hg])
  rw [heq]
  exact Subgroup.mem_zpowers h

theorem false_of_mem_isPGroup_two {Q : Subgroup G} (hQ : IsPGroup 2 Q) {c : G} (hc : c ∈ Q)
    (h5 : orderOf c = 5) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hQ ⟨c, hc⟩
  rw [Subgroup.orderOf_mk, h5] at hk
  have h5d : 5 ∣ 2 ^ k := hk ▸ dvd_refl 5
  have := (Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).mp
    ((by norm_num : Nat.Prime 5).dvd_of_dvd_pow h5d)
  omega

theorem exists_pow_of_mem_zpowers {g c : G} (hc : c ^ 5 = 1) (hg : g ∈ Subgroup.zpowers c) :
    ∃ m : ℕ, g = c ^ m := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  have hord : orderOf c ∣ 5 := orderOf_dvd_of_pow_eq_one hc
  have hpos : 0 < orderOf c := Nat.pos_of_ne_zero fun h0 => by
    rw [h0] at hord
    exact absurd (Nat.eq_zero_of_zero_dvd hord) (by norm_num)
  refine ⟨(k % (orderOf c : ℤ)).toNat, ?_⟩
  rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hpos.ne')),
    zpow_mod_orderOf]

theorem conj_automorphism_apply {V : Type*} [Group V] (σ : MulAut V) (v : V) :
    MulAut.conj (σ v) = σ * MulAut.conj v * σ⁻¹ := by
  ext w
  simp [MulAut.conj_apply]

theorem inv_mul_pow_mem_closure {V : Type*} [Group V] (β : MulAut V) (U : Subgroup V)
    (hU : ∀ u ∈ U, β u ∈ U) {u : V} (hu : u ∈ U) (n : ℕ) :
    u⁻¹ * (β ^ n) u ∈ Subgroup.closure {x | ∃ u ∈ U, x = u⁻¹ * β u} := by
  have hpow : ∀ m : ℕ, ∀ w ∈ U, (β ^ m) w ∈ U := by
    intro m
    induction m with
    | zero => intro w hw; simpa using hw
    | succ m ih => intro w hw; rw [pow_succ', MulAut.mul_apply]; exact hU _ (ih w hw)
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : u⁻¹ * (β ^ (n + 1)) u =
        (u⁻¹ * (β ^ n) u) * (((β ^ n) u)⁻¹ * β ((β ^ n) u)) := by
      rw [pow_succ', MulAut.mul_apply]
      group
    rw [h1]
    exact Subgroup.mul_mem _ ih (Subgroup.subset_closure ⟨(β ^ n) u, hpow n u hu, rfl⟩)

end CFSG.RankThree.PartOne.HNB
