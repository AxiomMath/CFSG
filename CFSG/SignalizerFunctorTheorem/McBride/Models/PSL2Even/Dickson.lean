module

import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonClassification
import CFSG.Walter.PSL2Facts.Even
import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Even.Arithmetic
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
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
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

namespace CFSG.SignalizerFunctorTheorem.McBride.PSL2Even

theorem subgroup_cases {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (H : Subgroup PSL(2, GaloisField 2 p)) :
    IsMulCommutative H ∨
      (∃ z : ℕ, (z ∣ 2 ^ p - 1 ∨ z ∣ 2 ^ p + 1) ∧ Nat.card H = 2 * z ∧
        Nonempty (H ≃* DihedralGroup z)) ∨
      (∃ m t : ℕ, m ≠ 0 ∧ t ∣ 2 ^ p - 1 ∧ Nat.card H = 2 ^ m * t) ∨
      (∃ m : ℕ, m ≠ 0 ∧ m ∣ p ∧ Nat.card H = 2 ^ m * ((2 ^ m) ^ 2 - 1) ∧
        Nonempty (H ≃* PSL(2, GaloisField 2 m))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 p) = 2 ^ p := GaloisField.card 2 p hp.ne_zero
  have hg : Nat.gcd (2 ^ p - 1) 2 = 1 := by
    refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr ?_)
    have := Nat.odd_iff.mp (odd_two_pow_sub_one hp.pos)
    omega
  rcases CFSG.Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hK H with
    hEl | ⟨z, -, -, hcyc⟩ | ⟨z, hz, hHz, hD⟩ | ⟨hA4, -⟩ | ⟨h16, -⟩ | ⟨hA5, -⟩ |
      ⟨m, t, -, ht, N, D, hN, -, hNcard, hDcyc, hDcard, hdisj, hsup⟩ | ⟨m, hm, hmp, ⟨eP⟩⟩ |
      ⟨m, -, hmp, -⟩
  · exact Or.inl hEl.toIsMulCommutative
  · exact Or.inl inferInstance
  · right; left
    refine ⟨z, ?_, hHz, hD⟩
    rw [hK, hg] at hz
    simpa using hz
  · exfalso
    rcases hA4 with h | h
    · exact h rfl
    · exact (Nat.not_even_iff_odd.mpr hodd) h
  · exact absurd h16 (not_sixteen_dvd hp.pos)
  · exfalso
    rcases hA5 with h | h
    · norm_num at h
    · exact not_five_dvd hodd h
  · rw [hg, Nat.div_one] at ht
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
    · right; right; left
      have : N.Normal := hN
      have hcompl : N.IsComplement' D := Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj
        (by rw [← Subgroup.normal_mul, hsup, Subgroup.coe_top])
      refine ⟨m, t, hm0, ht, ?_⟩
      rw [← hcompl.card_mul_card, hNcard, hDcard]
  · right; right; right
    refine ⟨m, hm, hmp, ?_, ⟨eP⟩⟩
    rw [Nat.card_congr eP.toEquiv, CFSG.Walter.psl2_even_card hm]
  · exfalso
    have h2 : 2 ∣ p := (dvd_mul_right 2 m).trans hmp
    obtain ⟨k, hk⟩ := hodd
    omega

theorem overgroup_cases {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    {C H : Subgroup PSL(2, GaloisField 2 p)} (hC : Nat.card C = 6)
    (hCnc : ∃ a ∈ C, ∃ b ∈ C, a * b ≠ b * a) (hCH : C ≤ H) (hH : H ≠ ⊤) :
    H = C ∨ ∃ z : ℕ, z ∣ 2 ^ p + 1 ∧ Nat.card H = 2 * z ∧ Nonempty (H ≃* DihedralGroup z) := by
  have h6 : 6 ∣ Nat.card H := hC ▸ Subgroup.card_dvd_of_le hCH
  have h3 : 3 ∣ Nat.card H := (by norm_num : 3 ∣ 6).trans h6
  rcases subgroup_cases hp hodd H with hcomm | ⟨z, hz, hHz, hD⟩ | ⟨m, t, -, ht, hHcard⟩ |
    ⟨m, hm, hmp, hHcard, ⟨eP⟩⟩
  · exfalso
    obtain ⟨a, ha, b, hb, hab⟩ := hCnc
    exact hab (congrArg Subtype.val (hcomm.is_comm.comm ⟨a, hCH ha⟩ ⟨b, hCH hb⟩))
  · right
    refine ⟨z, ?_, hHz, hD⟩
    rcases hz with hz | hz
    · exfalso
      rw [hHz] at h3
      have h3z : 3 ∣ z := by omega
      exact not_three_dvd_pow_sub_one hodd (h3z.trans hz)
    · exact hz
  · exfalso
    rw [hHcard] at h3
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h | h
    · have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
      omega
    · exact not_three_dvd_pow_sub_one hodd (h.trans ht)
  · rcases (Nat.dvd_prime hp).mp hmp with rfl | rfl
    · left
      have hcard : Nat.card H = 6 := by rw [hHcard]; norm_num
      exact (Subgroup.eq_of_le_of_card_ge hCH (by rw [hC, hcard])).symm
    · exfalso
      apply hH
      refine Subgroup.eq_top_of_card_eq H ?_
      rw [Nat.card_congr eP.toEquiv]

theorem card_dvd_of_overgroup {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    {C H : Subgroup PSL(2, GaloisField 2 p)} (hC : Nat.card C = 6)
    (hCnc : ∃ a ∈ C, ∃ b ∈ C, a * b ≠ b * a) (hCH : C ≤ H) (hH : H ≠ ⊤) :
    Nat.card H ∣ 2 * (2 ^ p + 1) := by
  rcases overgroup_cases hp hodd hC hCnc hCH hH with rfl | ⟨z, hz, hHz, -⟩
  · rw [hC]
    obtain ⟨k, hk⟩ := three_dvd_pow_add_one hodd
    exact ⟨k, by omega⟩
  · rw [hHz]
    exact Nat.mul_dvd_mul_left 2 hz

theorem isMulCommutative_of_odd_card
    {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (R : Subgroup PSL(2, GaloisField 2 p)) (hR : Odd (Nat.card R)) : IsMulCommutative R := by
  rcases subgroup_cases hp hodd R with hcomm | ⟨z, -, hHz, -⟩ | ⟨m, t, hm, -, hHcard⟩ |
    ⟨m, hm, -, hHcard, -⟩
  · exact hcomm
  · exfalso
    rw [hHz] at hR
    obtain ⟨k, hk⟩ := hR
    omega
  · exfalso
    rw [hHcard] at hR
    exact hm (eq_zero_of_odd_two_pow (Nat.odd_mul.mp hR).1)
  · exfalso
    rw [hHcard] at hR
    exact hm (eq_zero_of_odd_two_pow (Nat.odd_mul.mp hR).1)

theorem dihedral_conj_mem {Y : Type*} [Group Y] {H : Subgroup Y} {z : ℕ}
    (e : H ≃* DihedralGroup z) {c : Y} (hcH : c ∈ H) (hc : orderOf c = 3) :
    ∀ g ∈ H, g * c * g⁻¹ ∈ Subgroup.zpowers c := by
  obtain ⟨i, hi⟩ : ∃ i, e ⟨c, hcH⟩ = DihedralGroup.r i := by
    rcases h : e ⟨c, hcH⟩ with i | i
    · exact ⟨i, rfl⟩
    · exfalso
      have h3 : orderOf (e ⟨c, hcH⟩) = 3 := by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hc]
      rw [h, DihedralGroup.orderOf_sr] at h3
      omega
  intro g hg
  have key : (⟨g, hg⟩ : H) * ⟨c, hcH⟩ * (⟨g, hg⟩ : H)⁻¹ = ⟨c, hcH⟩ ∨
      (⟨g, hg⟩ : H) * ⟨c, hcH⟩ * (⟨g, hg⟩ : H)⁻¹ = (⟨c, hcH⟩ : H)⁻¹ := by
    rcases h : e ⟨g, hg⟩ with j | j
    · left
      apply e.injective
      rw [map_mul, map_mul, map_inv, h, hi, DihedralGroup.inv_r, DihedralGroup.r_mul_r,
        DihedralGroup.r_mul_r]
      congr 1
      ring
    · right
      apply e.injective
      rw [map_mul, map_mul, map_inv, map_inv, h, hi, DihedralGroup.sr_mul_r,
        DihedralGroup.inv_sr, DihedralGroup.sr_mul_sr, DihedralGroup.inv_r]
      congr 1
      ring
  rcases key with h | h
  · have := congrArg Subtype.val h
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
    rw [this]
    exact Subgroup.mem_zpowers c
  · have := congrArg Subtype.val h
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
    rw [this]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers c)

end CFSG.SignalizerFunctorTheorem.McBride.PSL2Even
