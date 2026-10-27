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

namespace CFSG.RankThree.PartOne

variable {G : Type*} [Group G]

theorem eq_zpowers_sup_of_card_eq_sq [Finite G] {p : ℕ} (hp : p.Prime) {E : Subgroup G}
    (hE : Nat.card E = p ^ 2) {c e : G} (hcE : c ∈ E) (heE : e ∈ E) (hc : orderOf c = p)
    (he : e ∉ Subgroup.zpowers c) : E = Subgroup.zpowers c ⊔ Subgroup.zpowers e := by
  set F := Subgroup.zpowers c ⊔ Subgroup.zpowers e with hF
  have hFE : F ≤ E := sup_le (Subgroup.zpowers_le.mpr hcE) (Subgroup.zpowers_le.mpr heE)
  have hcF : Subgroup.zpowers c ≤ F := le_sup_left
  have hcard : Nat.card (Subgroup.zpowers c) = p := by rw [Nat.card_zpowers, hc]
  have h1 : p ∣ Nat.card F := hcard ▸ Subgroup.card_dvd_of_le hcF
  have h2 : Nat.card F ∣ p ^ 2 := hE ▸ Subgroup.card_dvd_of_le hFE
  have hFcard : Nat.card F = p ^ 2 := by
    obtain ⟨k, hk, hkF⟩ := (Nat.dvd_prime_pow hp).mp h2
    interval_cases k
    · rw [hkF] at h1
      exact absurd (Nat.le_of_dvd one_pos (by simpa using h1)) (by have := hp.two_le; omega)
    · exfalso
      have heq : Subgroup.zpowers c = F :=
        Subgroup.eq_of_le_of_card_ge hcF (by rw [hcard, hkF, pow_one])
      exact he (heq ▸ (le_sup_right : Subgroup.zpowers e ≤ F) (Subgroup.mem_zpowers e))
    · exact hkF
  exact (Subgroup.eq_of_le_of_card_ge hFE (by rw [hE, hFcard])).symm

theorem eq_zpowers_of_le_of_card_eq_sq [Finite G] {p : ℕ} (hp : p.Prime) {E W : Subgroup G}
    (hWE : W ≤ E) (hE : Nat.card E = p ^ 2) {c e : G} (hcE : c ∈ E) (hcW : c ∉ W) (heW : e ∈ W)
    (he : orderOf e = p) : W = Subgroup.zpowers e := by
  have heW' : Subgroup.zpowers e ≤ W := Subgroup.zpowers_le.mpr heW
  have hcard : Nat.card (Subgroup.zpowers e) = p := by rw [Nat.card_zpowers, he]
  have h1 : p ∣ Nat.card W := hcard ▸ Subgroup.card_dvd_of_le heW'
  have h2 : Nat.card W ∣ p ^ 2 := hE ▸ Subgroup.card_dvd_of_le hWE
  obtain ⟨k, hk, hkW⟩ := (Nat.dvd_prime_pow hp).mp h2
  interval_cases k
  · rw [hkW] at h1
    exact absurd (Nat.le_of_dvd one_pos (by simpa using h1)) (by have := hp.two_le; omega)
  · exact (Subgroup.eq_of_le_of_card_ge heW' (by rw [hcard, hkW, pow_one])).symm
  · exfalso
    exact hcW (Subgroup.eq_of_le_of_card_ge hWE (by rw [hE, hkW]) ▸ hcE)

theorem orderOf_normalizerMonoidHom_eq {p : ℕ} (hp : p.Prime) {K : Subgroup G} {c : G}
    (hc : c ∈ Subgroup.normalizer (K : Set G)) (hord : orderOf c = p)
    (hcK : c ∉ Subgroup.centralizer (K : Set G)) :
    orderOf (K.normalizerMonoidHom ⟨c, hc⟩) = p := by
  have : Fact p.Prime := ⟨hp⟩
  apply orderOf_eq_prime
  · rw [← map_pow]
    have hcp : c ^ p = 1 := hord ▸ pow_orderOf_eq_one c
    have : (⟨c, hc⟩ : Subgroup.normalizer (K : Set G)) ^ p = 1 := Subtype.ext hcp
    rw [this, map_one]
  · intro h
    apply hcK
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have h2 := congrArg (fun φ : MulAut K => ((φ ⟨g, hg⟩ : K) : G)) h
    simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply] at h2
    calc g * c = (c * g * c⁻¹) * c := by rw [h2]
      _ = c * g := by group

end CFSG.RankThree.PartOne
