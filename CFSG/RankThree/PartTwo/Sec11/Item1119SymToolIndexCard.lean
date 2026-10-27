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

namespace CFSG.RankThree.PartTwo.Sec11.Item1119Sym

open scoped Pointwise

theorem relindex_le_three {G : Type*} [Group G] (R : Subgroup G) (g : G)
    (hg : g ∈ Subgroup.normalizer (R : Set G)) (hg3 : g ^ 3 = 1) :
    R.relIndex (R ⊔ Subgroup.zpowers g) ≤ 3 := by
  have hN : ∀ x ∈ Subgroup.normalizer (R : Set G), ∀ u ∈ R, x⁻¹ * u * x ∈ R :=
    fun x hx u hu => SetLike.mem_coe.mp ((Subgroup.mem_normalizer_iff''.mp hx u).mp
      (SetLike.mem_coe.mpr hu))
  have hLE : Subgroup.zpowers g ≤ Subgroup.normalizer (R : Set G) :=
    Subgroup.zpowers_le.mpr hg
  have hPeq : ((R ⊔ Subgroup.zpowers g : Subgroup G) : Set G) =
      (R : Set G) * (Subgroup.zpowers g : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left R (Subgroup.zpowers g) hLE
  have h3' : g ^ (3 : ℤ) = 1 := by exact_mod_cast hg3
  have hpow : ∀ k : ℤ, ∃ i : ℕ, i < 3 ∧ g ^ k = g ^ i := by
    intro k
    have hk : g ^ k = g ^ (k % 3) := by
      have hk' : k = k % 3 + 3 * (k / 3) := by omega
      conv_lhs => rw [hk']
      rw [zpow_add, zpow_mul, h3', one_zpow, mul_one]
    rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h | h | h
    · exact ⟨0, by norm_num, by simp [hk, h]⟩
    · exact ⟨1, by norm_num, by simp [hk, h]⟩
    · exact ⟨2, by norm_num, by simp [hk, h]⟩
  have hcov : ∀ p ∈ R ⊔ Subgroup.zpowers g, ∃ i : ℕ, i < 3 ∧ (g ^ i)⁻¹ * p ∈ R := by
    intro p hp
    have hp' : p ∈ ((R ⊔ Subgroup.zpowers g : Subgroup G) : Set G) := hp
    rw [hPeq] at hp'
    obtain ⟨u, hu, q, hq, rfl⟩ := Set.mem_mul.mp hp'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (SetLike.mem_coe.mp hq)
    obtain ⟨i, hi, hgk⟩ := hpow k
    refine ⟨i, hi, ?_⟩
    rw [hgk, ← mul_assoc]
    exact hN _ (pow_mem hg i) u (SetLike.mem_coe.mp hu)
  have hgP : g ∈ R ⊔ Subgroup.zpowers g := Subgroup.mem_sup_right (Subgroup.mem_zpowers g)
  let gP : ↥(R ⊔ Subgroup.zpowers g) := ⟨g, hgP⟩
  have hsurj : Function.Surjective (fun i : Fin 3 =>
      (QuotientGroup.mk (gP ^ (i : ℕ)) : ↥(R ⊔ Subgroup.zpowers g) ⧸
        R.subgroupOf (R ⊔ Subgroup.zpowers g))) := by
    intro q
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨i, hi, hmem⟩ := hcov p.1 p.2
    refine ⟨⟨i, hi⟩, ?_⟩
    dsimp only
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa [gP] using hmem
  rw [Subgroup.relIndex, Subgroup.index_eq_card]
  exact (Nat.card_le_card_of_surjective _ hsurj).trans (by simp)

theorem three_mul_card_le_of_lt {G : Type*} [Group G] [Finite G] (H K : Subgroup G)
    (hK : IsPGroup 3 K) (hHK : H < K) : 3 * Nat.card H ≤ Nat.card K := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hK
  have hcard : Nat.card H * (H.subgroupOf K).index = Nat.card K := by
    have h1 := Subgroup.card_mul_index (H.subgroupOf K)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK.le).toEquiv] at h1
    exact h1
  have hdvd : (H.subgroupOf K).index ∣ 3 ^ n := by
    rw [← hn]
    exact Subgroup.index_dvd_card (H.subgroupOf K)
  obtain ⟨m, _, hidx⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have hm : m ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hidx
    have htop := Subgroup.index_eq_one.mp hidx
    apply hHK.2
    intro x hx
    have hmem : (⟨x, hx⟩ : ↥K) ∈ H.subgroupOf K := by
      rw [htop]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hmem
  have h3 : 3 ≤ (H.subgroupOf K).index := by
    rw [hidx]
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
  calc 3 * Nat.card H = Nat.card H * 3 := mul_comm _ _
    _ ≤ Nat.card H * (H.subgroupOf K).index := Nat.mul_le_mul le_rfl h3
    _ = Nat.card K := hcard

end CFSG.RankThree.PartTwo.Sec11.Item1119Sym

end
