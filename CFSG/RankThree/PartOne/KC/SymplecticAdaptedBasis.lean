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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.RankThree.PartOne.KCSymplecticAdapted

open Module Matrix

section Abstract

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

structure Setup (ω : V →ₗ[K] V →ₗ[K] K) (N : V →ₗ[K] V) (c : Fin 4 → V) : Prop where
  alt : ∀ x, ω x x = 0
  nondeg : ∀ x, (∀ y, ω x y = 0) → x = 0
  skew : ∀ x y, ω (N x) y = - ω x (N y)
  li : LinearIndependent K c
  span : Submodule.span K (Set.range c) = ⊤

variable {ω : V →ₗ[K] V →ₗ[K] K} {N : V →ₗ[K] V} {c : Fin 4 → V}

namespace Setup

theorem comm (S : Setup ω N c) (x y : V) : ω x y = - ω y x := by
  have h := S.alt (x + y)
  simp only [map_add, LinearMap.add_apply, S.alt x, S.alt y, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_right h

theorem zero_of_perp (S : Setup ω N c) {w : V} (h : ∀ k, ω w (c k) = 0) : w = 0 := by
  apply S.nondeg
  have : ω w = 0 := LinearMap.ext_on_range S.span fun k => (h k).trans (LinearMap.zero_apply _).symm
  intro y
  rw [this]
  rfl

theorem zero_of_perp4 (S : Setup ω N c) {w : V} (h0 : ω w (c 0) = 0) (h1 : ω w (c 1) = 0)
    (h2 : ω w (c 2) = 0) (h3 : ω w (c 3) = 0) : w = 0 :=
  S.zero_of_perp fun k => by fin_cases k <;> assumption

theorem sq_adj (S : Setup ω N c) (x y : V) : ω (N (N x)) y = ω x (N (N y)) := by
  rw [S.skew (N x) y, S.skew x (N y), neg_neg]

theorem li4 (S : Setup ω N c) {x₀ x₁ x₂ x₃ : K}
    (h : x₀ • c 0 + x₁ • c 1 + x₂ • c 2 + x₃ • c 3 = 0) :
    x₀ = 0 ∧ x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0 := by
  have := Fintype.linearIndependent_iff.mp S.li ![x₀, x₁, x₂, x₃] (by
    simpa [Fin.sum_univ_four] using h)
  exact ⟨by simpa using this 0, by simpa using this 1, by simpa using this 2,
    by simpa using this 3⟩

theorem not_chain_three_one (S : Setup ω N c) (h2 : (2 : K) ≠ 0)
    (h0 : N (c 0) = 0) (h1 : N (c 1) = c 0) (h2' : N (c 2) = c 1) (h3 : N (c 3) = 0) :
    False := by
  have hc0 : c 0 = N (N (c 2)) := by rw [h2', h1]
  have e0 : ω (c 0) (c 0) = 0 := S.alt _
  have e1 : ω (c 0) (c 1) = 0 := by
    have h := S.sq_adj (c 2) (c 1)
    rw [← hc0, h1, h0, map_zero] at h
    exact h
  have e2 : ω (c 0) (c 2) = 0 := by
    have h := S.sq_adj (c 2) (c 2)
    rw [← hc0, S.comm (c 2) (c 0)] at h
    have h' : (2 : K) * ω (c 0) (c 2) = 0 := by linear_combination h
    exact (mul_eq_zero.mp h').resolve_left h2
  have e3 : ω (c 0) (c 3) = 0 := by
    have h := S.sq_adj (c 2) (c 3)
    rw [← hc0, h3, map_zero, map_zero] at h
    exact h
  exact S.li.ne_zero 0 (S.zero_of_perp fun k => by fin_cases k <;> simp [e0, e1, e2, e3])

theorem exists_adapted_transvection (S : Setup ω N c)
    (h0 : N (c 0) = 0) (h1 : N (c 1) = 0) (h2 : N (c 2) = 0) (h3 : N (c 3) = c 0) :
    ∃ (e f : Fin 2 → V) (γ : K), γ ≠ 0 ∧ (∀ i j, ω (e i) (e j) = 0) ∧
      (∀ i j, ω (f i) (f j) = 0) ∧ (∀ i j, ω (e i) (f j) = if i = j then 1 else 0) ∧
      N (e 0) = 0 ∧ N (e 1) = 0 ∧ N (f 1) = 0 ∧ N (f 0) = γ • e 0 := by
  have g00 : ω (c 0) (c 0) = 0 := S.alt _
  have g11 : ω (c 1) (c 1) = 0 := S.alt _
  have g22 : ω (c 2) (c 2) = 0 := S.alt _
  have g33 : ω (c 3) (c 3) = 0 := S.alt _
  have g01 : ω (c 0) (c 1) = 0 := by rw [← h3, S.skew, h1, map_zero, neg_zero]
  have g02 : ω (c 0) (c 2) = 0 := by rw [← h3, S.skew, h2, map_zero, neg_zero]
  have g10 : ω (c 1) (c 0) = 0 := by rw [S.comm, g01, neg_zero]
  have g20 : ω (c 2) (c 0) = 0 := by rw [S.comm, g02, neg_zero]
  have g30 : ω (c 3) (c 0) = - ω (c 0) (c 3) := S.comm _ _
  have g21 : ω (c 2) (c 1) = - ω (c 1) (c 2) := S.comm _ _
  have g31 : ω (c 3) (c 1) = - ω (c 1) (c 3) := S.comm _ _
  have g32 : ω (c 3) (c 2) = - ω (c 2) (c 3) := S.comm _ _
  obtain ⟨a, ha⟩ : ∃ a, a = ω (c 0) (c 3) := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, d = ω (c 1) (c 3) := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, m = ω (c 1) (c 2) := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = ω (c 2) (c 3) := ⟨_, rfl⟩
  rw [← ha] at g30
  rw [← hm] at g21
  rw [← hd] at g31
  rw [← hs] at g32
  have ha0 : a ≠ 0 := by
    intro h
    exact S.li.ne_zero 0 (S.zero_of_perp fun k => by
      fin_cases k <;> simp [g00, g01, g02, ← ha, h])
  have hai : a⁻¹ * a = 1 := inv_mul_cancel₀ ha0
  obtain ⟨t1, ht1⟩ : ∃ t1 : K, t1 = -(a⁻¹ * d) := ⟨_, rfl⟩
  obtain ⟨t2, ht2⟩ : ∃ t2 : K, t2 = -(a⁻¹ * s) := ⟨_, rfl⟩
  have pe0 : ω (c 1 + t1 • c 0) (c 0) = 0 := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, g10,
      g00]
    ring
  have pe1 : ω (c 1 + t1 • c 0) (c 1) = 0 := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, g11,
      g01]
    ring
  have pe2 : ω (c 1 + t1 • c 0) (c 2) = m := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, ← hm,
      g02]
    ring
  have pe3 : ω (c 1 + t1 • c 0) (c 3) = 0 := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, ← hd,
      ← ha]
    linear_combination a * ht1 - d * hai
  have hm0 : m ≠ 0 := by
    intro h
    have hz : c 1 + t1 • c 0 = 0 := S.zero_of_perp fun k => by
      fin_cases k
      · exact pe0
      · exact pe1
      · exact pe2.trans h
      · exact pe3
    have := S.li4 (x₀ := t1) (x₁ := 1) (x₂ := 0) (x₃ := 0) (by
      rw [one_smul, zero_smul, zero_smul, add_zero, add_zero, add_comm]
      exact hz)
    exact one_ne_zero this.2.1
  have hmi : m⁻¹ * m = 1 := inv_mul_cancel₀ hm0
  have pw0 : ω (c 2 + t2 • c 0) (c 0) = 0 := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, g20,
      g00]
    ring
  have pw1 : ω (c 2 + t2 • c 0) (c 1) = - m := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, g21,
      g01]
    ring
  have pw2 : ω (c 2 + t2 • c 0) (c 2) = 0 := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, g22,
      g02]
    ring
  have pw3 : ω (c 2 + t2 • c 0) (c 3) = 0 := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, ← hs,
      ← ha]
    linear_combination a * ht2 - s * hai
  have hee : ω (c 0) (c 1 + t1 • c 0) = 0 := by
    simp only [map_add, map_smul, smul_eq_mul, g01, g00]
    ring
  have hff : ω (a⁻¹ • c 3) (m⁻¹ • (c 2 + t2 • c 0)) = 0 := by
    simp only [map_add, map_smul, LinearMap.smul_apply, smul_eq_mul, g32, g30]
    rw [ht2]
    field_simp
    ring
  have hef00 : ω (c 0) (a⁻¹ • c 3) = 1 := by
    simp only [map_smul, smul_eq_mul, ← ha]
    exact hai
  have hef01 : ω (c 0) (m⁻¹ • (c 2 + t2 • c 0)) = 0 := by
    simp only [map_add, map_smul, smul_eq_mul, g02, g00]
    ring
  have hef10 : ω (c 1 + t1 • c 0) (a⁻¹ • c 3) = 0 := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, ← hd,
      ← ha]
    linear_combination (a * a⁻¹) * ht1 - d * a⁻¹ * hai
  have hef11 : ω (c 1 + t1 • c 0) (m⁻¹ • (c 2 + t2 • c 0)) = 1 := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, g10,
      g00, g02, ← hm]
    linear_combination hmi
  refine ⟨![c 0, c 1 + t1 • c 0], ![a⁻¹ • c 3, m⁻¹ • (c 2 + t2 • c 0)], a⁻¹, inv_ne_zero ha0,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j
    · exact g00
    · exact hee
    · exact pe0
    · exact S.alt _
  · intro i j
    fin_cases i <;> fin_cases j
    · exact S.alt _
    · exact hff
    · exact (S.comm (m⁻¹ • (c 2 + t2 • c 0)) (a⁻¹ • c 3)).trans (by rw [hff, neg_zero])
    · exact S.alt _
  · intro i j
    fin_cases i <;> fin_cases j
    · exact hef00
    · exact hef01
    · exact hef10
    · exact hef11
  · simpa using h0
  · simp [h1, h0]
  · simp [h2, h0]
  · simp [h3]

theorem exists_adapted_square_zero (S : Setup ω N c) (h2 : (2 : K) ≠ 0)
    (h0 : N (c 0) = 0) (h1 : N (c 1) = 0) (h2' : N (c 2) = c 0) (h3 : N (c 3) = c 1) :
    ∃ (e f : Fin 2 → V) (D : Matrix (Fin 2) (Fin 2) K), (∀ i j, ω (e i) (e j) = 0) ∧
      (∀ i j, ω (f i) (f j) = 0) ∧ (∀ i j, ω (e i) (f j) = if i = j then 1 else 0) ∧
      (∀ i, N (e i) = 0) ∧ (∀ j, N (f j) = ∑ i, D i j • e i) ∧ Dᵀ = D ∧ IsUnit D := by
  have g00 : ω (c 0) (c 0) = 0 := S.alt _
  have g11 : ω (c 1) (c 1) = 0 := S.alt _
  have g22 : ω (c 2) (c 2) = 0 := S.alt _
  have g33 : ω (c 3) (c 3) = 0 := S.alt _
  have g01 : ω (c 0) (c 1) = 0 := by
    rw [← h2', ← h3, S.skew, h3, h1, map_zero, neg_zero]
  have g10 : ω (c 1) (c 0) = 0 := by rw [S.comm, g01, neg_zero]
  have g12 : ω (c 1) (c 2) = ω (c 0) (c 3) := by
    rw [← h3, S.skew, h2', S.comm (c 3) (c 0), neg_neg]
  have g20 : ω (c 2) (c 0) = - ω (c 0) (c 2) := S.comm _ _
  have g30 : ω (c 3) (c 0) = - ω (c 0) (c 3) := S.comm _ _
  have g21 : ω (c 2) (c 1) = - ω (c 0) (c 3) := by rw [S.comm, g12]
  have g31 : ω (c 3) (c 1) = - ω (c 1) (c 3) := S.comm _ _
  have g32 : ω (c 3) (c 2) = - ω (c 2) (c 3) := S.comm _ _
  obtain ⟨a, ha⟩ : ∃ a, a = ω (c 0) (c 2) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = ω (c 0) (c 3) := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, d = ω (c 1) (c 3) := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = ω (c 2) (c 3) := ⟨_, rfl⟩
  rw [← ha] at g20
  rw [← hb] at g30 g21 g12
  rw [← hd] at g31
  rw [← hs] at g32
  have hΔ : a * d - b * b ≠ 0 := by
    intro hΔ
    by_cases hab : a = 0 ∧ b = 0
    · exact S.li.ne_zero 0 (S.zero_of_perp4 g00 g01 (by rw [← ha, hab.1]) (by rw [← hb, hab.2]))
    · have hz : b • c 0 + (-a) • c 1 = 0 := by
        refine S.zero_of_perp4 ?_ ?_ ?_ ?_
        · simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
            g00, g10]
          ring
        · simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
            g01, g11]
          ring
        · simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
            ← ha, g12]
          ring
        · simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
            ← hb, ← hd]
          linear_combination (-1 : K) * hΔ
      have := S.li4 (x₀ := b) (x₁ := -a) (x₂ := 0) (x₃ := 0) (by
        rw [zero_smul, zero_smul, add_zero, add_zero]
        exact hz)
      exact hab ⟨neg_eq_zero.mp this.2.1, this.1⟩
  obtain ⟨Δ, hΔdef⟩ : ∃ Δ, Δ = a * d - b * b := ⟨_, rfl⟩
  rw [← hΔdef] at hΔ
  have hΔi : Δ⁻¹ * Δ = 1 := inv_mul_cancel₀ hΔ
  obtain ⟨r, hr⟩ : ∃ r : K, r = s * Δ⁻¹ * 2⁻¹ := ⟨_, rfl⟩
  have h2i : (2 : K) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  have hff : ω ((d * Δ⁻¹) • c 2 + (-(b * Δ⁻¹)) • c 3 + (-r) • c 1)
      ((-(b * Δ⁻¹)) • c 2 + (a * Δ⁻¹) • c 3 + r • c 0) = 0 := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, g22, g33,
      g10, g12, g20, g30, g32, ← hd, ← hs]
    rw [hr]
    field_simp
    ring
  have hef00 : ω (c 0) ((d * Δ⁻¹) • c 2 + (-(b * Δ⁻¹)) • c 3 + (-r) • c 1) = 1 := by
    simp only [map_add, map_smul, smul_eq_mul, g01, ← ha, ← hb]
    linear_combination (-Δ⁻¹) * hΔdef + hΔi
  have hef01 : ω (c 0) ((-(b * Δ⁻¹)) • c 2 + (a * Δ⁻¹) • c 3 + r • c 0) = 0 := by
    simp only [map_add, map_smul, smul_eq_mul, g00, ← ha, ← hb]
    ring
  have hef10 : ω (c 1) ((d * Δ⁻¹) • c 2 + (-(b * Δ⁻¹)) • c 3 + (-r) • c 1) = 0 := by
    simp only [map_add, map_smul, smul_eq_mul, g11, g12, ← hd]
    ring
  have hef11 : ω (c 1) ((-(b * Δ⁻¹)) • c 2 + (a * Δ⁻¹) • c 3 + r • c 0) = 1 := by
    simp only [map_add, map_smul, smul_eq_mul, g10, g12, ← hd]
    linear_combination (-Δ⁻¹) * hΔdef + hΔi
  refine ⟨![c 0, c 1],
    ![(d * Δ⁻¹) • c 2 + (-(b * Δ⁻¹)) • c 3 + (-r) • c 1,
      (-(b * Δ⁻¹)) • c 2 + (a * Δ⁻¹) • c 3 + r • c 0],
    !![d * Δ⁻¹, -(b * Δ⁻¹); -(b * Δ⁻¹), a * Δ⁻¹], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j
    · exact g00
    · exact g01
    · exact g10
    · exact g11
  · intro i j
    fin_cases i <;> fin_cases j
    · exact S.alt _
    · exact hff
    · exact (S.comm ((-(b * Δ⁻¹)) • c 2 + (a * Δ⁻¹) • c 3 + r • c 0)
        ((d * Δ⁻¹) • c 2 + (-(b * Δ⁻¹)) • c 3 + (-r) • c 1)).trans (by rw [hff, neg_zero])
    · exact S.alt _
  · intro i j
    fin_cases i <;> fin_cases j
    · exact hef00
    · exact hef01
    · exact hef10
    · exact hef11
  · intro i
    fin_cases i
    · exact h0
    · exact h1
  · intro j
    fin_cases j
    · simp [Fin.sum_univ_two, map_add, map_smul, h1, h2', h3]
    · simp [Fin.sum_univ_two, map_add, map_smul, h0, h2', h3]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
  · rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_two_of, isUnit_iff_ne_zero]
    have : d * Δ⁻¹ * (a * Δ⁻¹) - -(b * Δ⁻¹) * -(b * Δ⁻¹) = Δ⁻¹ := by
      linear_combination (-Δ⁻¹ ^ 2) * hΔdef + Δ⁻¹ * hΔi
    rw [this]
    exact inv_ne_zero hΔ

end Setup

end Abstract

end CFSG.RankThree.PartOne.KCSymplecticAdapted
