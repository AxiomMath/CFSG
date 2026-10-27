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

namespace CFSG.RankThree.PartTwo.Sec16.ResGapFive.Pair

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G] {U Z : Subgroup G}

theorem comm_mul_left (hcomm : ∀ a ∈ U, ∀ b ∈ U, ⁅a, b⁆ ∈ Z)
    (hZc : ∀ z ∈ Z, ∀ g ∈ U, z * g = g * z) {a a' b : G} (ha : a ∈ U) (ha' : a' ∈ U)
    (hb : b ∈ U) : ⁅a * a', b⁆ = ⁅a, b⁆ * ⁅a', b⁆ := by
  have h1 := hZc _ (hcomm a' ha' b hb) a ha
  have hU : a * b * a⁻¹ * b⁻¹ ∈ U := mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have h2 := hZc _ (hcomm a' ha' b hb) (a * b * a⁻¹ * b⁻¹) hU
  simp only [commutatorElement_def] at h1 h2 ⊢
  calc a * a' * b * (a * a')⁻¹ * b⁻¹ = a * (a' * b * a'⁻¹ * b⁻¹) * b * a⁻¹ * b⁻¹ := by group
    _ = (a' * b * a'⁻¹ * b⁻¹) * a * b * a⁻¹ * b⁻¹ := by rw [← h1]
    _ = (a' * b * a'⁻¹ * b⁻¹) * (a * b * a⁻¹ * b⁻¹) := by group
    _ = (a * b * a⁻¹ * b⁻¹) * (a' * b * a'⁻¹ * b⁻¹) := h2

theorem comm_mul_right (hcomm : ∀ a ∈ U, ∀ b ∈ U, ⁅a, b⁆ ∈ Z)
    (hZc : ∀ z ∈ Z, ∀ g ∈ U, z * g = g * z) {a b b' : G} (ha : a ∈ U) (hb : b ∈ U)
    (hb' : b' ∈ U) : ⁅a, b * b'⁆ = ⁅a, b⁆ * ⁅a, b'⁆ := by
  have h1 := hZc _ (hcomm a ha b' hb') b hb
  simp only [commutatorElement_def] at h1 ⊢
  calc a * (b * b') * a⁻¹ * (b * b')⁻¹
      = (a * b * a⁻¹ * b⁻¹) * (b * (a * b' * a⁻¹ * b'⁻¹)) * b⁻¹ := by group
    _ = (a * b * a⁻¹ * b⁻¹) * ((a * b' * a⁻¹ * b'⁻¹) * b) * b⁻¹ := by rw [h1]
    _ = _ := by group

theorem comm_mul_central_left (hZc : ∀ z ∈ Z, ∀ g ∈ U, z * g = g * z) {a z b : G}
    (hz : z ∈ Z) (hb : b ∈ U) : ⁅a * z, b⁆ = ⁅a, b⁆ := by
  have h1 := hZc z hz b hb
  simp only [commutatorElement_def]
  calc a * z * b * (a * z)⁻¹ * b⁻¹ = a * (z * b) * z⁻¹ * a⁻¹ * b⁻¹ := by group
    _ = a * (b * z) * z⁻¹ * a⁻¹ * b⁻¹ := by rw [h1]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem comm_mul_central_right (hZc : ∀ z ∈ Z, ∀ g ∈ U, z * g = g * z) {a b z : G}
    (ha : a ∈ U) (hz : z ∈ Z) : ⁅a, b * z⁆ = ⁅a, b⁆ := by
  have h1 := hZc z hz a ha
  have h2 : z * a⁻¹ = a⁻¹ * z := by
    calc z * a⁻¹ = a⁻¹ * (a * z) * a⁻¹ := by group
      _ = a⁻¹ * (z * a) * a⁻¹ := by rw [h1]
      _ = a⁻¹ * z := by group
  simp only [commutatorElement_def]
  calc a * (b * z) * a⁻¹ * (b * z)⁻¹ = a * b * (z * a⁻¹) * z⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * z) * z⁻¹ * b⁻¹ := by rw [h2]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem inv_conj_eq {g : G} (hgZ : ∀ z ∈ Z, g * z * g⁻¹ = z) {z : G} (hz : z ∈ Z) :
    g⁻¹ * z * g = z := by
  calc g⁻¹ * z * g = g⁻¹ * (g * z * g⁻¹) * g := by rw [hgZ z hz]
    _ = z := by group

theorem comm_conj {g a y : G} (hgZ : ∀ z ∈ Z, g * z * g⁻¹ = z) (hmem : ⁅a, g⁻¹ * y * g⁆ ∈ Z) :
    ⁅g * a * g⁻¹, y⁆ = ⁅a, g⁻¹ * y * g⁆ := by
  have h1 := hgZ _ hmem
  rw [← h1]
  simp only [commutatorElement_def]
  group

theorem conj_mem {g : G} (hg : g ∈ normalizer (U : Set G)) {u : G} (hu : u ∈ U) :
    g * u * g⁻¹ ∈ U := (mem_normalizer_iff.mp hg u).mp hu

theorem conj_inv_mem {g : G} (hg : g ∈ normalizer (U : Set G)) {u : G} (hu : u ∈ U) :
    g⁻¹ * u * g ∈ U := by
  have := conj_mem (inv_mem hg) hu
  rwa [inv_inv] at this

theorem adjoint {g c : G} (hZU : Z ≤ U) (hcomm : ∀ a ∈ U, ∀ b ∈ U, ⁅a, b⁆ ∈ Z)
    (hZc : ∀ z ∈ Z, ∀ g ∈ U, z * g = g * z) (hgU : g ∈ normalizer (U : Set G))
    (hgZ : ∀ z ∈ Z, g * z * g⁻¹ = z)
    (hc : ∀ u ∈ U, (c * u * c⁻¹)⁻¹ * ((g * u * g⁻¹) * (g⁻¹ * u * g)) ∈ Z)
    {a w : G} (ha : a ∈ U) (hw : w ∈ U) :
    ⁅c * a * c⁻¹, w⁆ = ⁅a, c * w * c⁻¹⁆ := by
  have hga : g * a * g⁻¹ ∈ U := conj_mem hgU ha
  have hga' : g⁻¹ * a * g ∈ U := conj_inv_mem hgU ha
  have hgw : g * w * g⁻¹ ∈ U := conj_mem hgU hw
  have hgw' : g⁻¹ * w * g ∈ U := conj_inv_mem hgU hw
  have hza : ((g * a * g⁻¹) * (g⁻¹ * a * g))⁻¹ * (c * a * c⁻¹) ∈ Z := by
    have := inv_mem (hc a ha)
    simpa using this
  have hca : c * a * c⁻¹ =
      (g * a * g⁻¹) * (g⁻¹ * a * g) * (((g * a * g⁻¹) * (g⁻¹ * a * g))⁻¹ * (c * a * c⁻¹)) := by
    group
  have hzw := hc w hw
  have hcw : (g * w * g⁻¹) * (g⁻¹ * w * g) =
      c * w * c⁻¹ * ((c * w * c⁻¹)⁻¹ * ((g * w * g⁻¹) * (g⁻¹ * w * g))) := by group
  have hgZ' : ∀ z ∈ Z, g⁻¹ * z * g⁻¹⁻¹ = z := fun z hz => by
    rw [inv_inv]
    exact inv_conj_eq hgZ hz
  have hm1 : ⁅a, g⁻¹ * w * g⁆ ∈ Z := hcomm _ ha _ hgw'
  have hm2 : ⁅a, g⁻¹⁻¹ * w * g⁻¹⁆ ∈ Z := by
    rw [inv_inv]
    exact hcomm _ ha _ hgw
  have e1 := comm_conj hgZ hm1
  have e2 := comm_conj hgZ' hm2
  rw [inv_inv] at e2
  have h1 : ⁅a, g * w * g⁻¹⁆ * ⁅a, g⁻¹ * w * g⁆ = ⁅a, g⁻¹ * w * g⁆ * ⁅a, g * w * g⁻¹⁆ :=
    hZc _ (hcomm _ ha _ hgw) _ (hZU hm1)
  rw [hca, comm_mul_central_left hZc hza hw, comm_mul_left hcomm hZc hga hga' hw, e1, e2,
    ← h1, ← comm_mul_right hcomm hZc ha hgw hgw', hcw, comm_mul_central_right hZc ha hzw]

theorem conj_comm {g c : G} (hZU : Z ≤ U) (hcomm : ∀ a ∈ U, ∀ b ∈ U, ⁅a, b⁆ ∈ Z)
    (hZc : ∀ z ∈ Z, ∀ g ∈ U, z * g = g * z) (hgU : g ∈ normalizer (U : Set G))
    (hcU : c ∈ normalizer (U : Set G)) (hgZ : ∀ z ∈ Z, g * z * g⁻¹ = z)
    (hc : ∀ u ∈ U, (c * u * c⁻¹)⁻¹ * ((g * u * g⁻¹) * (g⁻¹ * u * g)) ∈ Z)
    {a y : G} (ha : a ∈ U) (hy : y ∈ U) :
    c * ⁅a, y⁆ * c⁻¹ = ⁅a, c * (c * y * c⁻¹) * c⁻¹⁆ := by
  have e : c * ⁅a, y⁆ * c⁻¹ = ⁅c * a * c⁻¹, c * y * c⁻¹⁆ := by
    simp only [commutatorElement_def]
    group
  rw [e, adjoint hZU hcomm hZc hgU hgZ hc ha (conj_mem hcU hy)]

theorem norm_comm {g c : G} (hZU : Z ≤ U) (hcomm : ∀ a ∈ U, ∀ b ∈ U, ⁅a, b⁆ ∈ Z)
    (hZc : ∀ z ∈ Z, ∀ g ∈ U, z * g = g * z) (hgU : g ∈ normalizer (U : Set G))
    (hcU : c ∈ normalizer (U : Set G)) (hgZ : ∀ z ∈ Z, g * z * g⁻¹ = z)
    (hc : ∀ u ∈ U, (c * u * c⁻¹)⁻¹ * ((g * u * g⁻¹) * (g⁻¹ * u * g)) ∈ Z) (hc3 : c ^ 3 = 1)
    (hcf : ∀ u ∈ U, c * u * c⁻¹ * u⁻¹ ∈ Z → u ∈ Z) {a y : G} (ha : a ∈ U) (hy : y ∈ U) :
    ⁅a, y⁆ * (c * ⁅a, y⁆ * c⁻¹) * (c * (c * ⁅a, y⁆ * c⁻¹) * c⁻¹) = 1 := by
  set y₁ := c * y * c⁻¹ with hy₁
  set y₂ := c * y₁ * c⁻¹ with hy₂
  have hy₁U : y₁ ∈ U := conj_mem hcU hy
  have hy₂U : y₂ ∈ U := conj_mem hcU hy₁U
  have hc3' : c * (c * c) = 1 := by rw [← hc3]; simp [pow_succ, mul_assoc]
  have hcy₂ : c * y₂ * c⁻¹ = y := by
    calc c * y₂ * c⁻¹ = (c * (c * c)) * y * (c * (c * c))⁻¹ := by rw [hy₂, hy₁]; group
      _ = y := by rw [hc3']; group
  have e1 : c * ⁅a, y⁆ * c⁻¹ = ⁅a, y₂⁆ := conj_comm hZU hcomm hZc hgU hcU hgZ hc ha hy
  have e2 : c * ⁅a, y₂⁆ * c⁻¹ = ⁅a, y₁⁆ := by
    rw [conj_comm hZU hcomm hZc hgU hcU hgZ hc ha hy₂U, hcy₂]
  rw [e1, e2, ← comm_mul_right hcomm hZc ha hy hy₂U,
    ← comm_mul_right hcomm hZc ha (mul_mem hy hy₂U) hy₁U]
  have hs : y * y₂ * y₁ ∈ Z := by
    refine hcf _ (mul_mem (mul_mem hy hy₂U) hy₁U) ?_
    have e : c * (y * y₂ * y₁) * c⁻¹ * (y * y₂ * y₁)⁻¹ = ⁅y₁, y * y₂⁆ := by
      have e' : c * (y * y₂ * y₁) * c⁻¹ =
          (c * y * c⁻¹) * (c * y₂ * c⁻¹) * (c * y₁ * c⁻¹) := by group
      rw [e', hcy₂, ← hy₂, ← hy₁]
      simp only [commutatorElement_def]
      group
    rw [e]
    exact hcomm _ hy₁U _ (mul_mem hy hy₂U)
  have h := hZc _ hs a ha
  rw [commutatorElement_def, ← h]
  group

theorem eq_one_of_fixed {g c : G} (hZU : Z ≤ U) (hcomm : ∀ a ∈ U, ∀ b ∈ U, ⁅a, b⁆ ∈ Z)
    (hZc : ∀ z ∈ Z, ∀ g ∈ U, z * g = g * z) (hZab : ∀ z ∈ Z, z * z = 1)
    (hgU : g ∈ normalizer (U : Set G)) (hcU : c ∈ normalizer (U : Set G))
    (hgZ : ∀ z ∈ Z, g * z * g⁻¹ = z)
    (hc : ∀ u ∈ U, (c * u * c⁻¹)⁻¹ * ((g * u * g⁻¹) * (g⁻¹ * u * g)) ∈ Z) (hc3 : c ^ 3 = 1)
    (hcf : ∀ u ∈ U, c * u * c⁻¹ * u⁻¹ ∈ Z → u ∈ Z) {φ : G} (hφ : φ ∈ ⁅U, U⁆)
    (hfix : c * φ * c⁻¹ = φ) : φ = 1 := by
  have hUU : ⁅U, U⁆ ≤ Z := by
    rw [commutator_le]
    intro a ha b hb
    exact hcomm a ha b hb
  have hZcomm : ∀ z ∈ Z, ∀ z' ∈ Z, z * z' = z' * z := fun z hz z' hz' => hZc z hz z' (hZU hz')
  have hcUU : ∀ ψ ∈ ⁅U, U⁆, c * ψ * c⁻¹ ∈ ⁅U, U⁆ := by
    intro ψ hψ
    rw [Subgroup.commutator_def] at hψ ⊢
    induction hψ using closure_induction with
    | mem ψ hψ =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hψ
      refine subset_closure ⟨c * a * c⁻¹, conj_mem hcU ha, c * b * c⁻¹, conj_mem hcU hb, ?_⟩
      simp only [commutatorElement_def]
      group
    | one => rw [mul_one, mul_inv_cancel]; exact one_mem _
    | mul a b _ _ ha hb =>
      rw [show c * (a * b) * c⁻¹ = (c * a * c⁻¹) * (c * b * c⁻¹) by group]
      exact mul_mem ha hb
    | inv a _ ha =>
      rw [show c * a⁻¹ * c⁻¹ = (c * a * c⁻¹)⁻¹ by group]
      exact inv_mem ha
  have hnorm : ∀ ψ ∈ ⁅U, U⁆, ψ * (c * ψ * c⁻¹) * (c * (c * ψ * c⁻¹) * c⁻¹) = 1 := by
    intro ψ hψ
    rw [Subgroup.commutator_def] at hψ
    induction hψ using closure_induction with
    | mem ψ hψ₀ =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hψ₀
      exact norm_comm hZU hcomm hZc hgU hcU hgZ hc hc3 hcf ha hb
    | one => group
    | mul a b ha' hb' h1 h2 =>
      have haU : a ∈ ⁅U, U⁆ := by rw [Subgroup.commutator_def]; exact ha'
      have hbU : b ∈ ⁅U, U⁆ := by rw [Subgroup.commutator_def]; exact hb'
      have hca := hcUU a haU
      have hcb := hcUU b hbU
      have hcca := hcUU _ hca
      have hb1 : b * (c * a * c⁻¹) = (c * a * c⁻¹) * b := hZcomm _ (hUU hbU) _ (hUU hca)
      have hb2 : b * (c * (c * a * c⁻¹) * c⁻¹) = (c * (c * a * c⁻¹) * c⁻¹) * b :=
        hZcomm _ (hUU hbU) _ (hUU hcca)
      have hb3 : (c * b * c⁻¹) * (c * (c * a * c⁻¹) * c⁻¹) =
          (c * (c * a * c⁻¹) * c⁻¹) * (c * b * c⁻¹) :=
        hZcomm _ (hUU hcb) _ (hUU hcca)
      calc a * b * (c * (a * b) * c⁻¹) * (c * (c * (a * b) * c⁻¹) * c⁻¹)
          = a * (b * (c * a * c⁻¹)) * (c * b * c⁻¹) * (c * (c * a * c⁻¹) * c⁻¹) *
              (c * (c * b * c⁻¹) * c⁻¹) := by group
        _ = a * (c * a * c⁻¹) * b * ((c * b * c⁻¹) * (c * (c * a * c⁻¹) * c⁻¹)) *
              (c * (c * b * c⁻¹) * c⁻¹) := by rw [hb1]; group
        _ = a * (c * a * c⁻¹) * (b * (c * (c * a * c⁻¹) * c⁻¹)) * (c * b * c⁻¹) *
              (c * (c * b * c⁻¹) * c⁻¹) := by rw [hb3]; group
        _ = (a * (c * a * c⁻¹) * (c * (c * a * c⁻¹) * c⁻¹)) *
              (b * (c * b * c⁻¹) * (c * (c * b * c⁻¹) * c⁻¹)) := by rw [hb2]; group
        _ = 1 := by rw [h1, h2, one_mul]
    | inv a ha' h1 =>
      have haU : a ∈ ⁅U, U⁆ := by rw [Subgroup.commutator_def]; exact ha'
      have hca := hcUU a haU
      have hc1 : a * (c * a * c⁻¹) = (c * a * c⁻¹) * a := hZcomm _ (hUU haU) _ (hUU hca)
      have hB : c * (c * a * c⁻¹) * c⁻¹ = (a * (c * a * c⁻¹))⁻¹ :=
        eq_inv_of_mul_eq_one_right h1
      calc a⁻¹ * (c * a⁻¹ * c⁻¹) * (c * (c * a⁻¹ * c⁻¹) * c⁻¹)
          = a⁻¹ * (c * a * c⁻¹)⁻¹ * (c * (c * a * c⁻¹) * c⁻¹)⁻¹ := by group
        _ = a⁻¹ * (c * a * c⁻¹)⁻¹ * (a * (c * a * c⁻¹)) := by rw [hB, inv_inv]
        _ = a⁻¹ * (c * a * c⁻¹)⁻¹ * ((c * a * c⁻¹) * a) := by rw [hc1]
        _ = 1 := by group
  have h1 := hnorm φ hφ
  rw [hfix, hfix] at h1
  have h2 := hZab φ (hUU hφ)
  calc φ = φ * φ * φ * (φ * φ)⁻¹ := by group
    _ = 1 := by rw [h1, h2, inv_one, mul_one]

end CFSG.RankThree.PartTwo.Sec16.ResGapFive.Pair
