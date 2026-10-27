module

public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism
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

namespace CFSG.RankThree.PartOne.KFOUT3

variable {K : Type} [Field K]

theorem exists_frobenius {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) :
    ∃ F : K ≃+* K, orderOf F = f ∧ Subgroup.zpowers F = ⊤ ∧ Nat.card (K ≃+* K) = f := by
  obtain ⟨F, -, h1, h2, h3, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two hf hK
  exact ⟨F, h1, h2, h3⟩

theorem aut_pow_card {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (σ : K ≃+* K) :
    σ ^ f = 1 := by
  obtain ⟨F, -, -, hcard⟩ := exists_frobenius hf hK
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  rw [← hcard]
  exact pow_card_eq_one'

theorem isCyclic_aut {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) : IsCyclic (K ≃+* K) := by
  obtain ⟨F, -, hF, -⟩ := exists_frobenius hf hK
  exact isCyclic_of_surjective (zpowersHom (K ≃+* K) F) (by
    intro x
    have : x ∈ Subgroup.zpowers F := by rw [hF]; exact Subgroup.mem_top x
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 this
    exact ⟨Multiplicative.ofAdd n, hn⟩)

theorem aut_pow_apply (τ : K ≃+* K) {z : K} {m : ℕ} (h : τ z = z ^ m) (n : ℕ) :
    (τ ^ n) z = z ^ (m ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, RingAut.mul_apply, h, map_pow, ih, ← pow_mul, pow_succ]

theorem three_dvd_of_pow_mod {p : ℕ} (hp : p.Prime) {k : ℕ} (hk1 : k % p ≠ 1) (hk3 : k ^ 3 % p = 1)
    {n : ℕ} (hn : k ^ n % p = 1) : 3 ∣ n := by
  have : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 % p = 1 := Nat.mod_eq_of_lt hp.one_lt
  have h3 : ((k : ZMod p)) ^ 3 = 1 := by
    have : ((k ^ 3 : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
      rw [ZMod.natCast_eq_natCast_iff', hk3, hp1]
    simpa using this
  have hn' : ((k : ZMod p)) ^ n = 1 := by
    have : ((k ^ n : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
      rw [ZMod.natCast_eq_natCast_iff', hn, hp1]
    simpa using this
  have hne : (k : ZMod p) ≠ 1 := by
    intro h
    apply hk1
    have : ((k : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by simpa using h
    rw [ZMod.natCast_eq_natCast_iff', hp1] at this
    exact this
  have h1 : orderOf (k : ZMod p) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have h2 : orderOf (k : ZMod p) = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 h1 with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hne
    · exact h
  rw [← h2]
  exact orderOf_dvd_of_pow_eq_one hn'

theorem aut_eq_one_of_three_power {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    {σ τ : K ≃+* K} {x : K} (hτ3 : τ ^ 3 = 1) (hτx : τ x ≠ x) {n : ℕ} (hσn : σ ^ (3 ^ n) = 1)
    (hσx : σ x = x) : σ = 1 := by
  have hcyc := isCyclic_aut hf hK
  have hfin : Finite (K ≃+* K) := by
    obtain ⟨F, -, -, hcard⟩ := exists_frobenius hf hK
    exact Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  by_contra hσ1
  have hτ1 : τ ≠ 1 := fun h => hτx (by rw [h]; rfl)
  have hordτ : orderOf τ = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime hτ3 hτ1
  obtain ⟨r, hr, hordσ⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hσn)
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hσ1 (orderOf_eq_one_iff.1 (by simpa using hordσ))
  have hdvd : 3 ∣ orderOf σ := by
    rw [hordσ]
    exact dvd_pow_self 3 hr0
  have hle : Subgroup.zpowers τ ≤ Subgroup.zpowers σ := by
    rw [IsCyclic.subgroup_le_iff_card_dvd, Nat.card_zpowers, Nat.card_zpowers, hordτ]
    exact hdvd
  let S : Subgroup (K ≃+* K) :=
    { carrier := {ρ | ρ x = x}
      mul_mem' := fun {a b} ha hb => by
        show a (b x) = x
        rw [show b x = x from hb, show a x = x from ha]
      one_mem' := rfl
      inv_mem' := fun {a} ha => by
        show a⁻¹ x = x
        rw [RingAut.inv_apply]
        exact a.symm_apply_eq.2 (show a x = x from ha).symm }
  have hSσ : Subgroup.zpowers σ ≤ S := (Subgroup.zpowers_le).2 hσx
  exact hτx (hSσ (hle (Subgroup.mem_zpowers τ)))

end CFSG.RankThree.PartOne.KFOUT3
