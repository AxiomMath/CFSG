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

namespace CFSG.Quasithin.ModH

section Count

variable {C : Type*} [Group C] [Finite C]

theorem false_of_comm_sylow_prime (hC : Nat.card C = 1920)
    (hodd : ∀ N : Subgroup C, N.Normal → Odd (Nat.card N) → N = ⊥)
    {T : Subgroup C} (hT : Nat.card T = 128) {d : ℕ} (hd : d = 3 ∨ d = 5) {g : C}
    (hg : ∀ t ∈ T, g * t = t * g) (hgd : orderOf g = d) : False := by
  have : Fact d.Prime := ⟨by rcases hd with rfl | rfl <;> norm_num⟩
  set Pd : Subgroup C := Subgroup.zpowers g with hPd
  have hPdcard : Nat.card Pd = d := by rw [hPd, Nat.card_zpowers, hgd]
  have hPdp : IsPGroup d Pd := IsPGroup.of_card (n := 1) (by rw [hPdcard, pow_one])
  have hidx : ¬ d ∣ Pd.index := by
    have h1 := Pd.card_mul_index
    rw [hPdcard, hC] at h1
    rcases hd with rfl | rfl
    · have : Pd.index = 640 := by omega
      rw [this]
      norm_num
    · have : Pd.index = 384 := by omega
      rw [this]
      norm_num
  let S : Sylow d C := hPdp.toSylow hidx
  have hS : (S : Subgroup C) = Pd := rfl
  have hmod : Nat.card (Sylow d C) ≡ 1 [MOD d] := card_sylow_modEq_one d C
  set N : Subgroup C := Subgroup.normalizer (Pd : Set C) with hN
  have hcardS : Nat.card (Sylow d C) = N.index := S.card_eq_index_normalizer
  have hTN : T ≤ N := by
    intro t ht
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact (Commute.zpow_left (show Commute g t from hg t ht) k).eq
  have hPN : Pd ≤ N := Subgroup.le_normalizer
  have h128 : 128 ∣ Nat.card N := by
    have := Subgroup.card_dvd_of_le hTN
    rwa [hT] at this
  have hdN : d ∣ Nat.card N := by
    have := Subgroup.card_dvd_of_le hPN
    rwa [hPdcard] at this
  have hcop : Nat.Coprime 128 d := by rcases hd with rfl | rfl <;> norm_num
  obtain ⟨m, hm⟩ := hcop.mul_dvd_of_dvd_of_dvd h128 hdN
  have hmul := N.card_mul_index
  rw [hm, hC] at hmul
  have hmod' : N.index ≡ 1 [MOD d] := hcardS ▸ hmod
  have hind1 : N.index = 1 := by
    generalize N.index = idx at hmul hmod'
    rcases hd with rfl | rfl
    · have h2 : 384 * (m * idx) = 1920 := by rw [← hmul]; ring
      have h3 : m * idx = 5 := by omega
      have hle : idx ≤ 5 := Nat.le_of_dvd (by norm_num) (Dvd.intro_left m h3)
      have hdvd : idx ∣ 5 := Dvd.intro_left m h3
      interval_cases idx <;> simp_all [Nat.ModEq]
    · have h2 : 640 * (m * idx) = 1920 := by rw [← hmul]; ring
      have h3 : m * idx = 3 := by omega
      have hle : idx ≤ 3 := Nat.le_of_dvd (by norm_num) (Dvd.intro_left m h3)
      have hdvd : idx ∣ 3 := Dvd.intro_left m h3
      interval_cases idx <;> simp_all [Nat.ModEq]
  have hnormal : Pd.Normal :=
    Subgroup.normalizer_eq_top_iff.1 (Subgroup.index_eq_one.1 hind1)
  have hodd' : Odd (Nat.card Pd) := by
    rw [hPdcard]
    rcases hd with rfl | rfl <;> decide
  have hbot := hodd Pd hnormal hodd'
  have hg1 : g = 1 := by
    have : g ∈ Pd := Subgroup.mem_zpowers g
    rw [hbot] at this
    exact Subgroup.mem_bot.1 this
  rw [hg1, orderOf_one] at hgd
  rcases hd with rfl | rfl <;> omega

theorem isPGroup_of_comm_sylow (hC : Nat.card C = 1920)
    (hodd : ∀ N : Subgroup C, N.Normal → Odd (Nat.card N) → N = ⊥)
    {T : Subgroup C} (hT : Nat.card T = 128) {g : C} (hg : ∀ t ∈ T, g * t = t * g) :
    IsPGroup 2 (Subgroup.zpowers g) := by
  rw [IsPGroup.iff_card, Nat.card_zpowers]
  have hpos : orderOf g ≠ 0 := (orderOf_pos g).ne'
  have hdvd : orderOf g ∣ 1920 := hC ▸ orderOf_dvd_natCard g
  refine ⟨(orderOf g).primeFactorsList.length, Nat.eq_prime_pow_of_unique_prime_dvd hpos ?_⟩
  intro d hd hdd
  by_contra hne
  have h15 : d ∣ 3 * 5 := by
    have h : d ∣ 2 ^ 7 * (3 * 5) := by simpa using hdd.trans hdvd
    rcases (Nat.Prime.dvd_mul hd).1 h with h2 | h2
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hd Nat.prime_two).1 (hd.dvd_of_dvd_pow h2)) hne
    · exact h2
  have hd35 : d = 3 ∨ d = 5 := by
    rcases (Nat.Prime.dvd_mul hd).1 h15 with h3 | h5
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hd (by norm_num)).1 h3)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hd (by norm_num)).1 h5)
  exact false_of_comm_sylow_prime hC hodd hT hd35 (g := g ^ (orderOf g / d))
    (fun t ht => (Commute.pow_left (show Commute g t from hg t ht) _).eq)
    (orderOf_pow_orderOf_div hpos hdd)

end Count

end CFSG.Quasithin.ModH
