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

namespace CFSG.RankThree.PartTwo.Sec20.Res3

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem le_normalizer_of_forall_conj_mem {H K : Subgroup G}
    (h : ∀ k ∈ K, ∀ x ∈ H, k * x * k⁻¹ ∈ H) : K ≤ Subgroup.normalizer (H : Set G) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h k hk x hx, fun hx => ?_⟩
  have h1 := h k⁻¹ (K.inv_mem hk) _ hx
  have h2 : k⁻¹ * (k * x * k⁻¹) * k⁻¹⁻¹ = x := by group
  rwa [h2] at h1

theorem commutatorElement_mul_right (x a b : G) :
    ⁅x, a * b⁆ = ⁅x, a⁆ * (a * ⁅x, b⁆ * a⁻¹) := by
  simp only [commutatorElement_def]
  group

theorem le_normalizer_commutator_right (X K : Subgroup G) :
    K ≤ Subgroup.normalizer ((⁅X, K⁆ : Subgroup G) : Set G) := by
  apply le_normalizer_of_forall_conj_mem
  intro k hk y hy
  have hle : ⁅X, K⁆ ≤ (⁅X, K⁆ : Subgroup G).comap (MulAut.conj k).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro x hx k' hk'
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have h2 : k * ⁅x, k'⁆ * k⁻¹ = ⁅x, k⁆⁻¹ * ⁅x, k * k'⁆ := by
      rw [commutatorElement_mul_right]
      group
    rw [h2]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hx hk))
      (Subgroup.commutator_mem_commutator hx (K.mul_mem hk hk'))
  have := hle hy
  rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this

theorem le_normalizer_commutator {H P Q : Subgroup G}
    (hP : H ≤ Subgroup.normalizer (P : Set G)) (hQ : H ≤ Subgroup.normalizer (Q : Set G)) :
    H ≤ Subgroup.normalizer ((⁅P, Q⁆ : Subgroup G) : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hP hh),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hQ hh)]

theorem commutator_le_of_le_of_le_normalizer {Ω W K : Subgroup G} (hWΩ : W ≤ Ω)
    (hKΩ : K ≤ Subgroup.normalizer (Ω : Set G)) : ⁅W, K⁆ ≤ Ω := by
  rw [Subgroup.commutator_le]
  intro w hw k hk
  have h1 : k * w⁻¹ * k⁻¹ ∈ Ω :=
    (Subgroup.mem_normalizer_iff.mp (hKΩ hk) _).mp (Ω.inv_mem (hWΩ hw))
  rw [commutatorElement_def, show w * k * w⁻¹ * k⁻¹ = w * (k * w⁻¹ * k⁻¹) by group]
  exact Ω.mul_mem (hWΩ hw) h1

theorem commutator_le_commutator_commutator {Ω X K : Subgroup G} {S : Set G}
    (hK : K = Subgroup.closure S) (hS : ∀ s ∈ S, s ^ 3 = 1)
    (hΩc : ∀ x ∈ Ω, ∀ y ∈ Ω, x * y = y * x) (hΩ2 : ∀ x ∈ Ω, x * x = 1)
    (hKΩ : K ≤ Subgroup.normalizer (Ω : Set G)) (hXΩ : X ≤ Ω) :
    ⁅X, K⁆ ≤ ⁅⁅X, K⁆, K⁆ := by
  set Y := ⁅⁅X, K⁆, K⁆ with hY
  have hXKΩ : ⁅X, K⁆ ≤ Ω := commutator_le_of_le_of_le_normalizer hXΩ hKΩ
  have hYΩ : Y ≤ Ω := commutator_le_of_le_of_le_normalizer hXKΩ hKΩ
  have hYK : ∀ k ∈ K, ∀ y ∈ Y, k * y * k⁻¹ ∈ Y := fun k hk y hy =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_commutator_right _ K hk) y).mp hy
  suffices H : ∀ k ∈ K, ∀ x ∈ X, ⁅x, k⁆ ∈ Y by
    rw [Subgroup.commutator_le]
    intro x hx k hk
    exact H k hk x hx
  intro k hk x hx
  have hkS : k ∈ Subgroup.closure S := hK ▸ hk
  clear hk
  induction hkS using Subgroup.closure_induction with
  | mem s hs =>
    have hsK : s ∈ K := hK ▸ Subgroup.subset_closure hs
    have hwXK : ⁅x, s⁆ ∈ ⁅X, K⁆ := Subgroup.commutator_mem_commutator hx hsK
    have hy₁Y : ⁅⁅x, s⁆⁻¹, s⁆ ∈ Y :=
      Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ hwXK) hsK
    have e4 : s * (s * s) = 1 := by
      rw [← pow_three]
      exact hS s hs
    have h0 : ⁅x, s * (s * s)⁆ = 1 := by
      rw [e4, commutatorElement_one_right]
    obtain ⟨w, hw⟩ : ∃ w, ⁅x, s⁆ = w := ⟨_, rfl⟩
    have e3 : ⁅x, s * (s * s)⁆ = w * (s * w * s⁻¹) * (s * (s * w * s⁻¹) * s⁻¹) := by
      rw [← hw]
      simp only [commutatorElement_def]
      group
    rw [hw] at hwXK hy₁Y
    obtain ⟨y₁, hy₁⟩ : ∃ y, ⁅w⁻¹, s⁆ = y := ⟨_, rfl⟩
    rw [hy₁] at hy₁Y
    have e1 : s * w * s⁻¹ = w * y₁ := by
      rw [← hy₁, commutatorElement_def]
      group
    have e5 : s * (w * y₁) * s⁻¹ = (s * w * s⁻¹) * (s * y₁ * s⁻¹) := by group
    rw [e3, e1, e5, e1] at h0
    have hwΩ : w ∈ Ω := hXKΩ hwXK
    have hy₂Y : s * y₁ * s⁻¹ ∈ Y := hYK s hsK y₁ hy₁Y
    have hc : y₁ * w = w * y₁ := hΩc _ (hYΩ hy₁Y) _ hwΩ
    have h2 : w * (w * y₁) * (w * y₁ * (s * y₁ * s⁻¹)) = w * (s * y₁ * s⁻¹) := by
      calc w * (w * y₁) * (w * y₁ * (s * y₁ * s⁻¹))
          = (w * w) * (y₁ * w) * y₁ * (s * y₁ * s⁻¹) := by group
        _ = (w * w) * (w * y₁) * y₁ * (s * y₁ * s⁻¹) := by rw [hc]
        _ = (w * w) * w * (y₁ * y₁) * (s * y₁ * s⁻¹) := by group
        _ = w * (s * y₁ * s⁻¹) := by rw [hΩ2 w hwΩ, hΩ2 y₁ (hYΩ hy₁Y)]; group
    rw [h2] at h0
    rw [hw, eq_inv_of_mul_eq_one_left h0]
    exact Subgroup.inv_mem _ hy₂Y
  | one =>
    rw [commutatorElement_def, mul_one, mul_inv_cancel, one_mul, inv_one]
    exact Subgroup.one_mem _
  | mul a b ha hb iha ihb =>
    rw [commutatorElement_mul_right]
    exact Subgroup.mul_mem _ iha (hYK a (hK ▸ ha) _ ihb)
  | inv a ha iha =>
    have e : ⁅x, a⁻¹⁆ = a⁻¹ * ⁅x, a⁆⁻¹ * a⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact hYK a⁻¹ (K.inv_mem (hK ▸ ha)) _ (Subgroup.inv_mem _ iha)

end CFSG.RankThree.PartTwo.Sec20.Res3
