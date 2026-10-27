module

import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonClassification
import CFSG.Walter.PSL2Facts.Odd
import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Three.A4
import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Three.Arithmetic
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
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
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
public import Mathlib.Topology.Sheaves.Presheaf

public section

open scoped MatrixGroups

namespace CFSG.SignalizerFunctorTheorem.McBride.PSL2Three

theorem subgroup_cases {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (H : Subgroup PSL(2, GaloisField 3 p)) :
    IsMulCommutative H ∨
      (∃ z : ℕ, (z ∣ (3 ^ p - 1) / 2 ∨ z ∣ (3 ^ p + 1) / 2) ∧ Nat.card H = 2 * z) ∨
      Nat.card H = 12 ∨
      (∃ m t : ℕ, m ≠ 0 ∧ t ∣ (3 ^ p - 1) / 2 ∧ Nat.card H = 3 ^ m * t) ∨
      (∃ m : ℕ, m ≠ 0 ∧ m ∣ p ∧ Nat.card H = 3 ^ m * ((3 ^ m) ^ 2 - 1) / 2) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK : Nat.card (GaloisField 3 p) = 3 ^ p := GaloisField.card 3 p hp.ne_zero
  have hg : Nat.gcd (3 ^ p - 1) 2 = 2 := by
    refine Nat.gcd_eq_right ?_
    obtain ⟨k, hk⟩ := odd_three_pow p
    exact ⟨k, by omega⟩
  rcases CFSG.Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hK H with
    hEl | ⟨z, -, -, hcyc⟩ | ⟨z, hz, hHz, -⟩ | ⟨-, ⟨eA4⟩⟩ | ⟨h16, -⟩ | ⟨h5, -⟩ |
      ⟨m, t, -, ht, N, D, hN, -, hNcard, hDcyc, hDcard, hdisj, hsup⟩ | ⟨m, hm, hmp, ⟨eP⟩⟩ |
      ⟨m, -, hmp, -⟩
  · exact Or.inl hEl.toIsMulCommutative
  · exact Or.inl inferInstance
  · right; left
    refine ⟨z, ?_, hHz⟩
    rw [hK, hg] at hz
    exact hz
  · right; right; left
    rw [Nat.card_congr eA4.toEquiv]
    exact a4_card
  · exact absurd h16 (not_sixteen_dvd hodd)
  · exfalso
    rcases h5 with h | h
    · norm_num at h
    · exact not_five_dvd hodd h
  · rw [hg] at ht
    by_cases hm0 : m = 0
    · left
      subst hm0
      rw [pow_zero] at hNcard
      have hNbot : N = ⊥ := Subgroup.card_eq_one.mp hNcard
      rw [hNbot, bot_sup_eq] at hsup
      refine ⟨⟨fun a b => ?_⟩⟩
      have ha : a ∈ D := hsup ▸ Subgroup.mem_top a
      have hb : b ∈ D := hsup ▸ Subgroup.mem_top b
      exact congrArg Subtype.val
        ((inferInstance : IsMulCommutative D).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    · right; right; right; left
      have : N.Normal := hN
      have hcompl : N.IsComplement' D := Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj
        (by rw [← Subgroup.normal_mul, hsup, Subgroup.coe_top])
      refine ⟨m, t, hm0, ht, ?_⟩
      rw [← hcompl.card_mul_card, hNcard, hDcard]
  · right; right; right; right
    refine ⟨m, hm, hmp, ?_⟩
    rw [Nat.card_congr eP.toEquiv,
      CFSG.GorensteinWalter.psl2_card_formula _
        (CFSG.Walter.isOddPrimePower_of_card (GaloisField.card 3 m hm) (by decide)
          (Nat.pos_of_ne_zero hm)),
      GaloisField.card 3 m hm]
  · exfalso
    have h2 : 2 ∣ p := (dvd_mul_right 2 m).trans hmp
    obtain ⟨k, hk⟩ := hodd
    omega

theorem eq_of_overgroup {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    {C H : Subgroup PSL(2, GaloisField 3 p)} (hC : Nat.card C = 12)
    (hCnc : ∃ a ∈ C, ∃ b ∈ C, a * b ≠ b * a) (hCH : C ≤ H) (hH : H ≠ ⊤) : H = C := by
  have h12 : 12 ∣ Nat.card H := hC ▸ Subgroup.card_dvd_of_le hCH
  have hp3 : 0 < p := hp.pos
  rcases subgroup_cases hp hodd H with hcomm | ⟨z, hz, hHz⟩ | hH12 | ⟨m, t, hm, ht, hHcard⟩ |
    ⟨m, hm, hmp, hHcard⟩
  · exfalso
    obtain ⟨a, ha, b, hb, hab⟩ := hCnc
    exact hab (congrArg Subtype.val (hcomm.is_comm.comm ⟨a, hCH ha⟩ ⟨b, hCH hb⟩))
  · exfalso
    rw [hHz] at h12
    have h6 : 6 ∣ z := by omega
    rcases hz with hz | hz
    · have h2 : 2 ∣ (3 ^ p - 1) / 2 := (dvd_trans (by norm_num : 2 ∣ 6) h6).trans hz
      exact (Nat.not_even_iff_odd.mpr (odd_three_pow_sub_one_div_two hodd))
        (even_iff_two_dvd.mpr h2)
    · have h3 : 3 ∣ (3 ^ p + 1) / 2 := (dvd_trans (by norm_num : 3 ∣ 6) h6).trans hz
      have : (3 ^ p + 1) / 2 ∣ 3 ^ p + 1 := Nat.div_dvd_of_dvd (by
        have := three_pow_mod_four hodd
        omega)
      exact not_three_dvd_three_pow_add_one hp3 (h3.trans this)
  · exact (Subgroup.eq_of_le_of_card_ge hCH (by rw [hC, hH12])).symm
  · exfalso
    rw [hHcard] at h12
    have h4 : 4 ∣ 3 ^ m * t := (by norm_num : 4 ∣ 12).trans h12
    have hcop : Nat.Coprime 4 (3 ^ m) := Nat.Coprime.pow_right m (by norm_num)
    have h4t : 4 ∣ t := hcop.dvd_of_dvd_mul_left h4
    have hodd' : Odd t := (odd_three_pow_sub_one_div_two hodd).of_dvd_nat ht
    exact (Nat.not_even_iff_odd.mpr hodd') (even_iff_two_dvd.mpr
      ((by norm_num : 2 ∣ 4).trans h4t))
  · rcases (Nat.dvd_prime hp).mp hmp with rfl | rfl
    · refine (Subgroup.eq_of_le_of_card_ge hCH ?_).symm
      rw [hC, hHcard]
      norm_num
    · exfalso
      apply hH
      refine Subgroup.eq_top_of_card_eq H ?_
      rw [hHcard, CFSG.GorensteinWalter.psl2_card_formula _
        (CFSG.Walter.isOddPrimePower_of_card (GaloisField.card 3 m hm) (by decide)
          (Nat.pos_of_ne_zero hm)), GaloisField.card 3 m hm]

theorem isMulCommutative_of_coprime_six
    {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (R : Subgroup PSL(2, GaloisField 3 p)) (hR : Nat.Coprime (Nat.card R) 6) :
    IsMulCommutative R := by
  rcases subgroup_cases hp hodd R with hcomm | ⟨z, -, hRz⟩ | hR12 | ⟨m, t, hm, -, hRcard⟩ |
    ⟨m, hm, -, hRcard⟩
  · exact hcomm
  · exfalso
    rw [hRz] at hR
    have := Nat.Coprime.coprime_dvd_left (dvd_mul_right 2 z) hR
    norm_num at this
  · exfalso
    rw [hR12] at hR
    norm_num at hR
  · exfalso
    rw [hRcard] at hR
    have := Nat.Coprime.coprime_dvd_left ((dvd_pow_self 3 hm).mul_right t) hR
    norm_num at this
  · exfalso
    rw [hRcard] at hR
    have h2 : 2 ∣ (3 ^ m) ^ 2 - 1 := by
      obtain ⟨a, ha⟩ := odd_three_pow m
      exact ⟨2 * a * a + 2 * a, by rw [ha]; ring_nf; omega⟩
    rw [Nat.mul_div_assoc _ h2] at hR
    have := Nat.Coprime.coprime_dvd_left ((dvd_pow_self 3 hm).mul_right _) hR
    norm_num at this

end CFSG.SignalizerFunctorTheorem.McBride.PSL2Three
