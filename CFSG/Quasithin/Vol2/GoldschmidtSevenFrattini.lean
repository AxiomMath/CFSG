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

namespace CFSG.Quasithin.H13.Seven

open Subgroup
open scoped Pointwise

theorem exists_conj_of_card_seven {X : Type} [Group X] [Finite X] (h49 : ¬ 49 ∣ Nat.card X)
    {M S S' : Subgroup X} (hS : S ≤ M) (hS' : S' ≤ M) (hc : Nat.card S = 7)
    (hc' : Nat.card S' = 7) : ∃ k ∈ M, ∀ s ∈ S', k * s * k⁻¹ ∈ S := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hMX : Nat.card M ∣ Nat.card X := Subgroup.card_subgroup_dvd_card M
  have h49M : ¬ 49 ∣ Nat.card M := fun h => h49 (h.trans hMX)
  have h7M : 7 ∣ Nat.card M := by
    have h := Subgroup.card_dvd_of_le hS
    rwa [hc] at h
  have hfac : (Nat.card M).factorization 7 = 1 := by
    have h1 : 0 < (Nat.card M).factorization 7 :=
      Nat.Prime.factorization_pos_of_dvd (by norm_num) Nat.card_pos.ne' h7M
    by_contra hne
    have h2 : 2 ≤ (Nat.card M).factorization 7 := by omega
    exact h49M (by
      have := (Nat.Prime.pow_dvd_iff_le_factorization (p := 7) (by norm_num)
        (n := Nat.card M) (k := 2) Nat.card_pos.ne').2 h2
      simpa using this)
  have hcS : Nat.card (S.subgroupOf M) = 7 ^ (Nat.card M).factorization 7 := by
    rw [hfac, pow_one, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS).toEquiv, hc]
  have hcS' : Nat.card (S'.subgroupOf M) = 7 ^ (Nat.card M).factorization 7 := by
    rw [hfac, pow_one, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS').toEquiv, hc']
  let P : Sylow 7 M := Sylow.ofCard (S.subgroupOf M) hcS
  let P' : Sylow 7 M := Sylow.ofCard (S'.subgroupOf M) hcS'
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq M P' P
  refine ⟨(k : X), k.2, fun s hs => ?_⟩
  have hsP' : (⟨s, hS' hs⟩ : M) ∈ (P' : Subgroup M) := hs
  have hmem : MulAut.conj k • (⟨s, hS' hs⟩ : M) ∈ MulAut.conj k • (P' : Subgroup M) :=
    smul_mem_pointwise_smul _ _ _ hsP'
  have hkP : MulAut.conj k • (P' : Subgroup M) = (P : Subgroup M) := by
    rw [← Sylow.coe_subgroup_smul, hk]
  rw [hkP] at hmem
  exact hmem

theorem exists_inverting_of_induced {X : Type} [Group X] [Finite X] (h49 : ¬ 49 ∣ Nat.card X)
    {Y : Subgroup X} {Λ : Type*} [Group Λ] (ρ : ↥Y →* Λ) (hρ : Function.Surjective ρ)
    {n : X} (hn : n ∈ Subgroup.normalizer (Y : Set X)) (ι : Λ ≃* Λ)
    (hι : ∀ y y' : ↥Y, (y' : X) = n * y * n⁻¹ → ρ y' = ι (ρ y))
    {a : Λ} (ha : orderOf a = 7) (hia : ι a = a⁻¹) :
    ∃ x g : X, orderOf x = 7 ∧ g * x * g⁻¹ = x⁻¹ := by
  have hp7 : Nat.Prime 7 := by norm_num
  obtain ⟨y₁, hy₁⟩ := hρ a
  have h7dvd : 7 ∣ orderOf y₁ := by
    have h := orderOf_map_dvd ρ y₁
    rwa [hy₁, ha] at h
  obtain ⟨r, hr⟩ := h7dvd
  have hr7 : ¬ 7 ∣ r := by
    intro h7r
    apply h49
    have hX : orderOf y₁ ∣ Nat.card Y := orderOf_dvd_natCard y₁
    have hYX : Nat.card Y ∣ Nat.card X := Subgroup.card_subgroup_dvd_card Y
    have h49' : 49 ∣ orderOf y₁ := by
      rw [hr]
      obtain ⟨s, rfl⟩ := h7r
      exact ⟨s, by ring⟩
    exact h49'.trans (hX.trans hYX)
  have hr0 : r ≠ 0 := by
    rintro rfl
    have : 0 < orderOf y₁ := orderOf_pos y₁
    omega
  set y : ↥Y := y₁ ^ r with hy
  have hyord : orderOf y = 7 := by
    rw [hy, orderOf_pow_of_dvd hr0 ⟨7, by rw [hr, mul_comm]⟩, hr]
    exact Nat.mul_div_cancel 7 (Nat.pos_of_ne_zero hr0)
  set ā : Λ := a ^ r with hā
  have hρy : ρ y = ā := by rw [hy, map_pow, hy₁]
  have hāord : orderOf ā = 7 := by
    rw [hā]
    exact Nat.Coprime.orderOf_pow (by rw [ha]; exact (hp7.coprime_iff_not_dvd).2 hr7) |>.trans ha
  have hιā : ι ā = ā⁻¹ := by rw [hā, map_pow, hia, inv_pow]
  have hny : n * (y : X) * n⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.1 hn (y : X)).1 y.2
  set y'' : ↥Y := ⟨n * (y : X) * n⁻¹, hny⟩ with hy''
  have hρy'' : ρ y'' = ā⁻¹ := by
    rw [hι y y'' rfl, hρy, hιā]
  set S : Subgroup X := zpowers (y : X) with hS
  set S' : Subgroup X := zpowers ((y'' : ↥Y) : X) with hS'
  set M : Subgroup X := (Subgroup.comap ρ (zpowers ā)).map Y.subtype with hM
  have hyX : orderOf (y : X) = 7 := by rw [Subgroup.orderOf_coe, hyord]
  have hy''ord : orderOf (y'' : X) = 7 := by
    have : (y'' : X) = (MulAut.conj n).toMonoidHom (y : X) := rfl
    rw [this, orderOf_injective _ (MulAut.conj n).injective, hyX]
  have hcS : Nat.card S = 7 := by rw [hS, Nat.card_zpowers, hyX]
  have hcS' : Nat.card S' = 7 := by rw [hS', Nat.card_zpowers, hy''ord]
  have hSM : S ≤ M := by
    rw [hS, Subgroup.zpowers_le]
    exact ⟨y, by simp [hρy], rfl⟩
  have hS'M : S' ≤ M := by
    rw [hS', Subgroup.zpowers_le]
    exact ⟨y'', by simp [hρy''], rfl⟩
  obtain ⟨k, hkM, hk⟩ := exists_conj_of_card_seven h49 hSM hS'M hcS hcS'
  obtain ⟨k', hk'ρ, rfl⟩ := hkM
  have hconj : (k' : X) * (y'' : X) * (k' : X)⁻¹ ∈ S := hk _ (Subgroup.mem_zpowers _)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hconj
  have hzj : k' * y'' * k'⁻¹ = y ^ j := by
    apply Subtype.ext
    simpa using hj.symm
  have hρk' : ρ k' ∈ zpowers ā := hk'ρ
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hρk'
  have hρz : ρ (k' * y'' * k'⁻¹) = ā⁻¹ := by
    rw [map_mul, map_mul, map_inv, hρy'', ← hi]
    group
  have hρyj : ρ (y ^ j) = ā ^ j := by rw [map_zpow, hρy]
  have hj1 : ā ^ (j + 1) = 1 := by
    rw [zpow_add_one, ← hρyj, ← hzj, hρz, inv_mul_cancel]
  have hdvd : (7 : ℤ) ∣ j + 1 := by
    have := orderOf_dvd_iff_zpow_eq_one.2 hj1
    rwa [hāord] at this
  have hyj : y ^ (j + 1) = 1 :=
    orderOf_dvd_iff_zpow_eq_one.1 (by rw [hyord]; exact_mod_cast hdvd)
  have hyj' : y ^ j = y⁻¹ := by
    rw [zpow_add_one] at hyj
    exact eq_inv_of_mul_eq_one_left hyj
  refine ⟨(y : X), (k' : X) * n, hyX, ?_⟩
  have h1 : ((k' * y'' * k'⁻¹ : ↥Y) : X) = (y : X)⁻¹ := by
    rw [hzj, hyj']
    rfl
  rw [← h1]
  simp [hy'', mul_assoc]

end CFSG.Quasithin.H13.Seven
