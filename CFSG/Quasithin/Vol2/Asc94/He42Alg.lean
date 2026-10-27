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

namespace CFSG.Quasithin.A94.He42Alg

variable {Γ : Type*} [Group Γ]

private lemma he42al_conj_self {l y : Γ} (h : l * y = y * l) : l * y * l⁻¹ = y := by
  rw [h, mul_inv_cancel_right]

private lemma he42al_zpow_cube {y : Γ} (h : y ^ 3 = 1) (k : ℤ) : (y ^ k) ^ 3 = 1 := by
  rw [← zpow_natCast (y ^ k) 3, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h, one_zpow]

private lemma he42al_cube_comm {L y₁ y₂ : Γ} (hL1 : L * y₁ * L⁻¹ = y₂)
    (hL2 : L * y₂ * L⁻¹ = (y₁ * y₂)⁻¹) :
    L ^ 3 * y₁ = y₁ * L ^ 3 ∧ L ^ 3 * y₂ = y₂ * L ^ 3 := by
  have hL3 : L * (y₁ * y₂)⁻¹ * L⁻¹ = y₁ := by
    calc L * (y₁ * y₂)⁻¹ * L⁻¹ = (L * y₂ * L⁻¹)⁻¹ * (L * y₁ * L⁻¹)⁻¹ := by group
      _ = y₁ := by rw [hL1, hL2, inv_inv, mul_inv_cancel_right]
  have e1 : L * y₁ = y₂ * L := mul_inv_eq_iff_eq_mul.mp hL1
  have e2 : L * y₂ = (y₁ * y₂)⁻¹ * L := mul_inv_eq_iff_eq_mul.mp hL2
  have e3 : L * (y₁ * y₂)⁻¹ = y₁ * L := mul_inv_eq_iff_eq_mul.mp hL3
  constructor
  · calc L ^ 3 * y₁ = L * (L * (L * y₁)) := by simp only [pow_three', mul_assoc]
      _ = L * (L * (y₂ * L)) := by rw [e1]
      _ = L * (L * y₂) * L := by simp only [mul_assoc]
      _ = L * ((y₁ * y₂)⁻¹ * L) * L := by rw [e2]
      _ = (L * (y₁ * y₂)⁻¹) * L * L := by simp only [mul_assoc]
      _ = (y₁ * L) * L * L := by rw [e3]
      _ = y₁ * L ^ 3 := by simp only [pow_three', mul_assoc]
  · calc L ^ 3 * y₂ = L * (L * (L * y₂)) := by simp only [pow_three', mul_assoc]
      _ = L * (L * ((y₁ * y₂)⁻¹ * L)) := by rw [e2]
      _ = L * ((L * (y₁ * y₂)⁻¹) * L) := by simp only [mul_assoc]
      _ = L * ((y₁ * L) * L) := by rw [e3]
      _ = (L * y₁) * L * L := by simp only [mul_assoc]
      _ = (y₂ * L) * L * L := by rw [e1]
      _ = y₂ * L ^ 3 := by simp only [pow_three', mul_assoc]

theorem l1_conj_y2 {y₁ y₂ l₁ : Γ} (hy : y₁ * y₂ = y₂ * y₁) (h1 : y₁ ^ 3 = 1)
    (hl₁y₁ : l₁ * y₁ = y₁ * l₁) (hl₁y₀ : l₁ * (y₁ * y₂⁻¹) * l₁⁻¹ = (y₁ * y₂⁻¹)⁻¹) :
    l₁ * y₂ * l₁⁻¹ = (y₁ * y₂)⁻¹ := by
  have hc1 : l₁ * y₁ * l₁⁻¹ = y₁ := he42al_conj_self hl₁y₁
  have hcomm : Commute y₁ y₂⁻¹ := (show Commute y₁ y₂ from hy).inv_right
  have hy1inv : y₁ * y₁ = y₁⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_three']; exact h1)
  have key : y₁ * (l₁ * y₂⁻¹ * l₁⁻¹) = (y₁ * y₂⁻¹)⁻¹ := by
    calc y₁ * (l₁ * y₂⁻¹ * l₁⁻¹) = (l₁ * y₁ * l₁⁻¹) * (l₁ * y₂⁻¹ * l₁⁻¹) := by rw [hc1]
      _ = l₁ * (y₁ * y₂⁻¹) * l₁⁻¹ := by group
      _ = (y₁ * y₂⁻¹)⁻¹ := hl₁y₀
  have hX : l₁ * y₂⁻¹ * l₁⁻¹ = y₁⁻¹ * (y₁ * y₂⁻¹)⁻¹ := eq_inv_mul_iff_mul_eq.mpr key
  have hA : l₁ * y₂ * l₁⁻¹ = y₁ * y₂⁻¹ * y₁ := by
    calc l₁ * y₂ * l₁⁻¹ = (l₁ * y₂⁻¹ * l₁⁻¹)⁻¹ := by group
      _ = (y₁⁻¹ * (y₁ * y₂⁻¹)⁻¹)⁻¹ := by rw [hX]
      _ = y₁ * y₂⁻¹ * y₁ := by group
  have hfin : y₁ * y₂⁻¹ * y₁ = (y₁ * y₂)⁻¹ := by
    calc y₁ * y₂⁻¹ * y₁ = (y₂⁻¹ * y₁) * y₁ := by rw [hcomm.eq]
      _ = y₂⁻¹ * (y₁ * y₁) := mul_assoc _ _ _
      _ = y₂⁻¹ * y₁⁻¹ := by rw [hy1inv]
      _ = (y₁ * y₂)⁻¹ := (mul_inv_rev y₁ y₂).symm
  exact hA.trans hfin

theorem l2_conj_y1 {y₁ y₂ l₂ : Γ} (hy : y₁ * y₂ = y₂ * y₁) (h2 : y₂ ^ 3 = 1)
    (hl₂y₂ : l₂ * y₂ = y₂ * l₂) (hl₂y₀ : l₂ * (y₁ * y₂⁻¹) * l₂⁻¹ = (y₁ * y₂⁻¹)⁻¹) :
    l₂ * y₁ * l₂⁻¹ = (y₁ * y₂)⁻¹ := by
  have hc2 : l₂ * y₂ * l₂⁻¹ = y₂ := he42al_conj_self hl₂y₂
  have hc2' : l₂ * y₂⁻¹ * l₂⁻¹ = y₂⁻¹ := by
    calc l₂ * y₂⁻¹ * l₂⁻¹ = (l₂ * y₂ * l₂⁻¹)⁻¹ := by group
      _ = y₂⁻¹ := by rw [hc2]
  have hkey : (l₂ * y₁ * l₂⁻¹) * y₂⁻¹ = (y₁ * y₂⁻¹)⁻¹ := by
    calc (l₂ * y₁ * l₂⁻¹) * y₂⁻¹ = (l₂ * y₁ * l₂⁻¹) * (l₂ * y₂⁻¹ * l₂⁻¹) := by rw [hc2']
      _ = l₂ * (y₁ * y₂⁻¹) * l₂⁻¹ := by group
      _ = (y₁ * y₂⁻¹)⁻¹ := hl₂y₀
  have hX : l₂ * y₁ * l₂⁻¹ = y₂ * y₁⁻¹ * y₂ := by
    calc l₂ * y₁ * l₂⁻¹ = ((l₂ * y₁ * l₂⁻¹) * y₂⁻¹) * y₂ := by group
      _ = (y₁ * y₂⁻¹)⁻¹ * y₂ := by rw [hkey]
      _ = y₂ * y₁⁻¹ * y₂ := by group
  have hcomm : Commute y₁⁻¹ y₂ := (show Commute y₁ y₂ from hy).inv_left
  have hy2inv : y₂ * y₂ = y₂⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_three']; exact h2)
  calc l₂ * y₁ * l₂⁻¹ = y₂ * y₁⁻¹ * y₂ := hX
    _ = y₂ * (y₁⁻¹ * y₂) := mul_assoc _ _ _
    _ = y₂ * (y₂ * y₁⁻¹) := by rw [hcomm.eq]
    _ = (y₂ * y₂) * y₁⁻¹ := (mul_assoc _ _ _).symm
    _ = y₂⁻¹ * y₁⁻¹ := by rw [hy2inv]
    _ = (y₁ * y₂)⁻¹ := (mul_inv_rev y₁ y₂).symm

theorem l_conj_y1 {y₁ y₂ l₁ l₂ : Γ} (hy : y₁ * y₂ = y₂ * y₁) (h1 : y₁ ^ 3 = 1) (h2 : y₂ ^ 3 = 1)
    (hl₁y₁ : l₁ * y₁ = y₁ * l₁) (hl₁y₀ : l₁ * (y₁ * y₂⁻¹) * l₁⁻¹ = (y₁ * y₂⁻¹)⁻¹)
    (hl₂y₂ : l₂ * y₂ = y₂ * l₂) (hl₂y₀ : l₂ * (y₁ * y₂⁻¹) * l₂⁻¹ = (y₁ * y₂⁻¹)⁻¹) :
    (l₁ * l₂) * y₁ * (l₁ * l₂)⁻¹ = y₂ := by
  have hc1 : l₁ * y₁ * l₁⁻¹ = y₁ := he42al_conj_self hl₁y₁
  have hA : l₁ * y₂ * l₁⁻¹ = (y₁ * y₂)⁻¹ := l1_conj_y2 hy h1 hl₁y₁ hl₁y₀
  have hB : l₂ * y₁ * l₂⁻¹ = (y₁ * y₂)⁻¹ := l2_conj_y1 hy h2 hl₂y₂ hl₂y₀
  calc (l₁ * l₂) * y₁ * (l₁ * l₂)⁻¹ = l₁ * (l₂ * y₁ * l₂⁻¹) * l₁⁻¹ := by group
    _ = l₁ * (y₁ * y₂)⁻¹ * l₁⁻¹ := by rw [hB]
    _ = (l₁ * y₂ * l₁⁻¹)⁻¹ * (l₁ * y₁ * l₁⁻¹)⁻¹ := by group
    _ = y₂ := by rw [hA, hc1, inv_inv, hy, mul_inv_cancel_right]

theorem l_conj_y2 {y₁ y₂ l₁ l₂ : Γ} (hy : y₁ * y₂ = y₂ * y₁) (h1 : y₁ ^ 3 = 1) (h2 : y₂ ^ 3 = 1)
    (hl₁y₁ : l₁ * y₁ = y₁ * l₁) (hl₁y₀ : l₁ * (y₁ * y₂⁻¹) * l₁⁻¹ = (y₁ * y₂⁻¹)⁻¹)
    (hl₂y₂ : l₂ * y₂ = y₂ * l₂) (hl₂y₀ : l₂ * (y₁ * y₂⁻¹) * l₂⁻¹ = (y₁ * y₂⁻¹)⁻¹) :
    (l₁ * l₂) * y₂ * (l₁ * l₂)⁻¹ = (y₁ * y₂)⁻¹ := by
  calc (l₁ * l₂) * y₂ * (l₁ * l₂)⁻¹ = l₁ * (l₂ * y₂ * l₂⁻¹) * l₁⁻¹ := by group
    _ = l₁ * y₂ * l₁⁻¹ := by rw [he42al_conj_self hl₂y₂]
    _ = (y₁ * y₂)⁻¹ := l1_conj_y2 hy h1 hl₁y₁ hl₁y₀

theorem l_cube_comm {y₁ y₂ l₁ l₂ : Γ} (hy : y₁ * y₂ = y₂ * y₁) (h1 : y₁ ^ 3 = 1) (h2 : y₂ ^ 3 = 1)
    (hl₁y₁ : l₁ * y₁ = y₁ * l₁) (hl₁y₀ : l₁ * (y₁ * y₂⁻¹) * l₁⁻¹ = (y₁ * y₂⁻¹)⁻¹)
    (hl₂y₂ : l₂ * y₂ = y₂ * l₂) (hl₂y₀ : l₂ * (y₁ * y₂⁻¹) * l₂⁻¹ = (y₁ * y₂⁻¹)⁻¹) :
    (l₁ * l₂) ^ 3 * y₁ = y₁ * (l₁ * l₂) ^ 3 ∧ (l₁ * l₂) ^ 3 * y₂ = y₂ * (l₁ * l₂) ^ 3 :=
  he42al_cube_comm (l_conj_y1 hy h1 h2 hl₁y₁ hl₁y₀ hl₂y₂ hl₂y₀)
    (l_conj_y2 hy h1 h2 hl₁y₁ hl₁y₀ hl₂y₂ hl₂y₀)

theorem commutator_comm {y₁ y₂ l v : Γ} (hy : y₁ * y₂ = y₂ * y₁) (h1 : y₁ ^ 3 = 1)
    (h2 : y₂ ^ 3 = 1) (hv : v * v = 1) (hv₁ : v * y₁ * v⁻¹ = y₁⁻¹) (hv₂ : v * y₂ * v⁻¹ = y₂⁻¹)
    (hl₁ : l * y₁ * l⁻¹ = y₂) (hl₂ : l * y₂ * l⁻¹ = (y₁ * y₂)⁻¹) :
    (v * l * v⁻¹ * l⁻¹) * y₁ = y₁ * (v * l * v⁻¹ * l⁻¹) ∧
      (v * l * v⁻¹ * l⁻¹) * y₂ = y₂ * (v * l * v⁻¹ * l⁻¹) := by
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  have hF : l⁻¹ * y₂ * l = y₁ := by
    calc l⁻¹ * y₂ * l = l⁻¹ * (l * y₁ * l⁻¹) * l := by rw [hl₁]
      _ = y₁ := by group
  have hD : l * (y₁ * y₂) * l⁻¹ = y₁⁻¹ := by
    calc l * (y₁ * y₂) * l⁻¹ = (l * y₁ * l⁻¹) * (l * y₂ * l⁻¹) := by group
      _ = y₂ * (y₁ * y₂)⁻¹ := by rw [hl₁, hl₂]
      _ = y₁⁻¹ := by group
  have hA : l * (y₁ * y₂)⁻¹ * l⁻¹ = y₁ := by
    calc l * (y₁ * y₂)⁻¹ * l⁻¹ = (l * (y₁ * y₂) * l⁻¹)⁻¹ := by group
      _ = y₁ := by rw [hD, inv_inv]
  have hB : l⁻¹ * y₁ * l = (y₁ * y₂)⁻¹ := by
    calc l⁻¹ * y₁ * l = l⁻¹ * (l * (y₁ * y₂)⁻¹ * l⁻¹) * l := by rw [hA]
      _ = (y₁ * y₂)⁻¹ := by group
  have hE : v * y₁⁻¹ * v⁻¹ = y₁ := by
    calc v * y₁⁻¹ * v⁻¹ = (v * y₁ * v⁻¹)⁻¹ := by group
      _ = y₁ := by rw [hv₁, inv_inv]
  have hE2 : v * y₂⁻¹ * v⁻¹ = y₂ := by
    calc v * y₂⁻¹ * v⁻¹ = (v * y₂ * v⁻¹)⁻¹ := by group
      _ = y₂ := by rw [hv₂, inv_inv]
  have hC : v⁻¹ * (y₁ * y₂)⁻¹ * v = y₁ * y₂ := by
    calc v⁻¹ * (y₁ * y₂)⁻¹ * v = v * (y₁ * y₂)⁻¹ * v⁻¹ := by rw [hvinv]
      _ = (v * y₂⁻¹ * v⁻¹) * (v * y₁⁻¹ * v⁻¹) := by group
      _ = y₂ * y₁ := by rw [hE2, hE]
      _ = y₁ * y₂ := hy.symm
  have hG : v⁻¹ * y₁ * v = y₁⁻¹ := by
    calc v⁻¹ * y₁ * v = v * y₁ * v⁻¹ := by rw [hvinv]
      _ = y₁⁻¹ := hv₁
  have hH : l * y₁⁻¹ * l⁻¹ = y₂⁻¹ := by
    calc l * y₁⁻¹ * l⁻¹ = (l * y₁ * l⁻¹)⁻¹ := by group
      _ = y₂⁻¹ := by rw [hl₁]
  have hcy1 : (v * l * v⁻¹ * l⁻¹) * y₁ * (v * l * v⁻¹ * l⁻¹)⁻¹ = y₁ := by
    calc (v * l * v⁻¹ * l⁻¹) * y₁ * (v * l * v⁻¹ * l⁻¹)⁻¹
        = v * (l * (v⁻¹ * (l⁻¹ * y₁ * l) * v) * l⁻¹) * v⁻¹ := by group
      _ = v * (l * (v⁻¹ * (y₁ * y₂)⁻¹ * v) * l⁻¹) * v⁻¹ := by rw [hB]
      _ = v * (l * (y₁ * y₂) * l⁻¹) * v⁻¹ := by rw [hC]
      _ = v * y₁⁻¹ * v⁻¹ := by rw [hD]
      _ = y₁ := hE
  have hcy2 : (v * l * v⁻¹ * l⁻¹) * y₂ * (v * l * v⁻¹ * l⁻¹)⁻¹ = y₂ := by
    calc (v * l * v⁻¹ * l⁻¹) * y₂ * (v * l * v⁻¹ * l⁻¹)⁻¹
        = v * (l * (v⁻¹ * (l⁻¹ * y₂ * l) * v) * l⁻¹) * v⁻¹ := by group
      _ = v * (l * (v⁻¹ * y₁ * v) * l⁻¹) * v⁻¹ := by rw [hF]
      _ = v * (l * y₁⁻¹ * l⁻¹) * v⁻¹ := by rw [hG]
      _ = v * y₂⁻¹ * v⁻¹ := by rw [hH]
      _ = y₂ := hE2
  exact ⟨mul_inv_eq_iff_eq_mul.mp hcy1, mul_inv_eq_iff_eq_mul.mp hcy2⟩

private lemma he42al_zpow_cube_comm {y₀ l : Γ} (hly : l * y₀ = y₀ * l) (k : ℤ) :
    Commute (y₀ ^ k) l :=
  Commute.zpow_left (show Commute y₀ l from hly.symm) k

theorem pow_three_eq_one {y₀ l v : Γ} (hv : v * v = 1) (hvy : v * y₀ * v⁻¹ = y₀⁻¹)
    (hy3 : y₀ ^ 3 = 1) (hy1 : y₀ ≠ 1) (hly : l * y₀ = y₀ * l)
    (hl3 : l ^ 3 ∈ Subgroup.zpowers y₀) (hvl : ∃ t ∈ Subgroup.zpowers y₀, v * l * v⁻¹ = t * l) :
    l ^ 3 = 1 := by
  by_contra hz
  obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp hl3
  obtain ⟨t, ht, hvt⟩ := hvl
  obtain ⟨b, hb⟩ := Subgroup.mem_zpowers_iff.mp ht
  have hcomm : Commute (y₀ ^ b) l := he42al_zpow_cube_comm hly b
  have hw : v * l * v⁻¹ = y₀ ^ b * l := by rw [hvt, hb]
  have h1 : v * l ^ 3 * v⁻¹ = l ^ 3 := by
    rw [← conj_pow, hw, hcomm.mul_pow, he42al_zpow_cube hy3 b, one_mul]
  have h3 : v * y₀ ^ a * v⁻¹ = y₀ ^ (-a) := by
    rw [← conj_zpow, hvy, zpow_neg, inv_zpow]
  rw [← ha, h3] at h1
  rw [zpow_neg] at h1
  have hg2 : y₀ ^ a * y₀ ^ a = 1 := inv_eq_iff_mul_eq_one.mp h1
  have hg1 : y₀ ^ a = 1 := by
    have e : (y₀ ^ a) ^ 3 = y₀ ^ a := by rw [pow_three', hg2, one_mul]
    exact e.symm.trans (he42al_zpow_cube hy3 a)
  exact hz (ha.symm.trans hg1)

theorem conj_comm_l2 {y₁ y₂ l₂ u : Γ} (hl₂ : l₂ * l₂ = 1) (h : l₂ * y₁ * l₂⁻¹ = (y₁ * y₂)⁻¹)
    (hu : u * y₁ = y₁ * u) : (l₂⁻¹ * u * l₂) * (y₁ * y₂) = (y₁ * y₂) * (l₂⁻¹ * u * l₂) := by
  have hinv : l₂⁻¹ = l₂ := inv_eq_of_mul_eq_one_right hl₂
  have hX : l₂⁻¹ * y₁ * l₂ = (y₁ * y₂)⁻¹ := by
    calc l₂⁻¹ * y₁ * l₂ = l₂ * y₁ * l₂⁻¹ := by rw [hinv]
      _ = (y₁ * y₂)⁻¹ := h
  have hcomm : (l₂⁻¹ * u * l₂) * (l₂⁻¹ * y₁ * l₂) = (l₂⁻¹ * y₁ * l₂) * (l₂⁻¹ * u * l₂) := by
    calc (l₂⁻¹ * u * l₂) * (l₂⁻¹ * y₁ * l₂) = l₂⁻¹ * (u * y₁) * l₂ := by group
      _ = l₂⁻¹ * (y₁ * u) * l₂ := by rw [hu]
      _ = (l₂⁻¹ * y₁ * l₂) * (l₂⁻¹ * u * l₂) := by group
  have hc : Commute (l₂⁻¹ * u * l₂) (y₁ * y₂)⁻¹ := by
    show (l₂⁻¹ * u * l₂) * (y₁ * y₂)⁻¹ = (y₁ * y₂)⁻¹ * (l₂⁻¹ * u * l₂)
    rw [← hX]
    exact hcomm
  have hc2 := hc.inv_right
  rw [inv_inv] at hc2
  exact hc2

theorem conj_comm_l1 {y₁ y₂ l₁ u : Γ} (hl₁ : l₁ * l₁ = 1) (h : l₁ * y₂ * l₁⁻¹ = (y₁ * y₂)⁻¹)
    (hu : u * y₂ = y₂ * u) : (l₁⁻¹ * u * l₁) * (y₁ * y₂) = (y₁ * y₂) * (l₁⁻¹ * u * l₁) := by
  have hinv : l₁⁻¹ = l₁ := inv_eq_of_mul_eq_one_right hl₁
  have hX : l₁⁻¹ * y₂ * l₁ = (y₁ * y₂)⁻¹ := by
    calc l₁⁻¹ * y₂ * l₁ = l₁ * y₂ * l₁⁻¹ := by rw [hinv]
      _ = (y₁ * y₂)⁻¹ := h
  have hcomm : (l₁⁻¹ * u * l₁) * (l₁⁻¹ * y₂ * l₁) = (l₁⁻¹ * y₂ * l₁) * (l₁⁻¹ * u * l₁) := by
    calc (l₁⁻¹ * u * l₁) * (l₁⁻¹ * y₂ * l₁) = l₁⁻¹ * (u * y₂) * l₁ := by group
      _ = l₁⁻¹ * (y₂ * u) * l₁ := by rw [hu]
      _ = (l₁⁻¹ * y₂ * l₁) * (l₁⁻¹ * u * l₁) := by group
  have hc : Commute (l₁⁻¹ * u * l₁) (y₁ * y₂)⁻¹ := by
    show (l₁⁻¹ * u * l₁) * (y₁ * y₂)⁻¹ = (y₁ * y₂)⁻¹ * (l₁⁻¹ * u * l₁)
    rw [← hX]
    exact hcomm
  have hc2 := hc.inv_right
  rw [inv_inv] at hc2
  exact hc2

end CFSG.Quasithin.A94.He42Alg
