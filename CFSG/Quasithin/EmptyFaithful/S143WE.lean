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

namespace CFSG.Quasithin

open scoped commutatorElement

namespace S143W

theorem prime_dvd_720 {p : ℕ} (hp : p.Prime) (h : p ∣ 720) : p = 2 ∨ p = 3 ∨ p = 5 := by
  have h720 : (720 : ℕ) = 2 ^ 4 * 3 ^ 2 * 5 := by norm_num
  rw [h720] at h
  rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2))
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
        (hp.dvd_of_dvd_pow h2)))
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp h1))

theorem exists_normal_nine_of_solvable {Γ : Type*} [Group Γ] [Finite Γ] [Group.IsSolvable Γ]
    (hO2 : ∀ N : Subgroup Γ, N.Normal → IsPGroup 2 N → N = ⊥) (hdvd : Nat.card Γ ∣ 720)
    {Pd : Subgroup Γ} (hPd : Pd ≠ ⊥)
    (hno : ∀ N : Subgroup Γ, N.Normal → N ≤ Pd → Nat.card N ≠ 3 ∧ Nat.card N ≠ 5)
    (hPdn : Pd.Normal) :
    ∃ E : Subgroup Γ, E.Normal ∧ E ≤ Pd ∧ Nat.card E = 9 := by
  classical
  have hne : ∃ n, ∃ N : Subgroup Γ, N.Normal ∧ N ≤ Pd ∧ N ≠ ⊥ ∧ Nat.card N = n :=
    ⟨_, Pd, hPdn, le_rfl, hPd, rfl⟩
  obtain ⟨N₀, hN₀n, hN₀P, hN₀1, hN₀c⟩ := Nat.find_spec hne
  have hmin : ∀ N : Subgroup Γ, N.Normal → N ≤ Pd → N ≠ ⊥ → Nat.card N₀ ≤ Nat.card N := by
    intro N hN hNP hN1
    rw [hN₀c]
    exact Nat.find_min' hne ⟨N, hN, hNP, hN1, rfl⟩
  have hcomm : ⁅N₀, N₀⁆ = ⊥ := by
    by_contra hc
    have hlt : ⁅N₀, N₀⁆ < N₀ := Group.IsSolvable.commutator_lt_of_ne_bot hN₀1
    have hnorm : (⁅N₀, N₀⁆).Normal := Subgroup.commutator_normal N₀ N₀
    have h1 := hmin ⁅N₀, N₀⁆ hnorm (hlt.le.trans hN₀P) hc
    have h2 : Nat.card ↥(⁅N₀, N₀⁆ : Subgroup Γ) < Nat.card N₀ := by
      by_contra hge
      exact hlt.ne (Subgroup.eq_of_le_of_card_ge hlt.le (not_lt.mp hge))
    omega
  have hab : ∀ x ∈ N₀, ∀ y ∈ N₀, x * y = y * x := by
    intro x hx y hy
    have : ⁅x, y⁆ ∈ ⁅N₀, N₀⁆ := Subgroup.commutator_mem_commutator hx hy
    rw [hcomm, Subgroup.mem_bot, commutatorElement_def] at this
    calc x * y = (x * y * x⁻¹ * y⁻¹) * y * x := by group
      _ = y * x := by rw [this]; group
  have hcard1 : 1 < Nat.card N₀ := (Subgroup.one_lt_card_iff_ne_bot N₀).mpr hN₀1
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (show Nat.card N₀ ≠ 1 by omega)
  have : Fact p.Prime := ⟨hp⟩
  let Ω : Subgroup Γ :=
    { carrier := {x | x ∈ N₀ ∧ x ^ p = 1}
      mul_mem' := by
        rintro x y ⟨hx, hx1⟩ ⟨hy, hy1⟩
        refine ⟨N₀.mul_mem hx hy, ?_⟩
        rw [(show Commute x y from hab x hx y hy).mul_pow, hx1, hy1, one_mul]
      one_mem' := ⟨N₀.one_mem, one_pow p⟩
      inv_mem' := by
        rintro x ⟨hx, hx1⟩
        exact ⟨N₀.inv_mem hx, by rw [inv_pow, hx1, inv_one]⟩ }
  have hΩle : Ω ≤ N₀ := fun x hx => hx.1
  have hΩn : Ω.Normal := by
    refine ⟨fun x hx γ => ⟨hN₀n.conj_mem x hx.1 γ, ?_⟩⟩
    rw [conj_pow, hx.2]
    simp
  have hΩ1 : Ω ≠ ⊥ := by
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := N₀) p hpd
    intro hbot
    have hxΩ : (x : Γ) ∈ Ω := ⟨x.2, by
      have : orderOf (x : Γ) = p := by rw [Subgroup.orderOf_coe]; exact hx
      rw [← this]
      exact pow_orderOf_eq_one _⟩
    rw [hbot, Subgroup.mem_bot] at hxΩ
    have : orderOf (x : Γ) = 1 := by rw [hxΩ]; exact orderOf_one
    rw [Subgroup.orderOf_coe, hx] at this
    exact hp.one_lt.ne' this
  have hΩc : Nat.card Ω = Nat.card N₀ :=
    le_antisymm (Subgroup.card_le_of_le hΩle) (hmin Ω hΩn (hΩle.trans hN₀P) hΩ1)
  have hΩeq : Ω = N₀ := Subgroup.eq_of_le_of_card_ge hΩle hΩc.ge
  have hexp : ∀ x ∈ N₀, x ^ p = 1 := fun x hx => by
    have : x ∈ Ω := hΩeq ▸ hx
    exact this.2
  have hpgrp : IsPGroup p N₀ := fun x => ⟨1, by
    apply Subtype.ext
    simpa using hexp x x.2⟩
  obtain ⟨n, hn⟩ := hpgrp.exists_card_eq
  have hN₀d : Nat.card N₀ ∣ 720 := (Subgroup.card_subgroup_dvd_card N₀).trans hdvd
  have hpd720 : p ∣ 720 := hpd.trans hN₀d
  rcases prime_dvd_720 hp hpd720 with rfl | rfl | rfl
  · exact absurd (hO2 N₀ hN₀n hpgrp) hN₀1
  ·
    obtain _ | _ | _ | n := n
    · rw [pow_zero] at hn
      omega
    · exact absurd (by simpa using hn) (hno N₀ hN₀n hN₀P).1
    · exact ⟨N₀, hN₀n, hN₀P, by simpa using hn⟩
    · exfalso
      have h27 : 3 ^ 3 ∣ 3 ^ (n + 3) := pow_dvd_pow 3 (by omega)
      rw [← hn] at h27
      have := h27.trans hN₀d
      omega
  ·
    obtain _ | _ | n := n
    · rw [pow_zero] at hn
      omega
    · exact absurd (by simpa using hn) (hno N₀ hN₀n hN₀P).2
    · exfalso
      have h25 : 5 ^ 2 ∣ 5 ^ (n + 2) := pow_dvd_pow 5 (by omega)
      rw [← hn] at h25
      have := h25.trans hN₀d
      omega

end S143W

end CFSG.Quasithin
