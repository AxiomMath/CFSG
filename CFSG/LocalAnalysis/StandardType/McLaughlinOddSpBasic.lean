module

public import CFSG.LocalAnalysis.StandardType.McLaughlinOddBasic
public import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

public section

namespace CFSG.StandardType.McLaughlinOdd

open CFSG.RankThree.PartOne.LIT

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
  {H : Subgroup (V ≃ₗ[ZMod p] V)}

theorem two_ne_zero_of_ne_two (hp : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h0
  have h3 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
  rw [ZMod.natCast_eq_zero_iff] at h3
  have h4 := Nat.le_of_dvd (by norm_num) h3
  have h5 := (Fact.out : p.Prime).two_le
  omega

structure IsSpBlock (H : Subgroup (V ≃ₗ[ZMod p] V)) (W L : Submodule (ZMod p) V)
    (β : LinearMap.BilinForm (ZMod p) V) : Prop where
  compl : IsCompl W L
  alt : β.IsAlt
  vanish : ∀ x, ∀ l ∈ L, β x l = 0
  nondeg : ∀ w ∈ W, w ≠ 0 → ∃ w' ∈ W, β w w' ≠ 0
  trIn : ∀ w ∈ W, TrIn H w (β.flip w)

theorem isSpBlock_bot : IsSpBlock H ⊥ ⊤ (0 : LinearMap.BilinForm (ZMod p) V) where
  compl := isCompl_bot_top
  alt := LinearMap.BilinForm.isAlt_zero
  vanish := fun _ _ _ => rfl
  nondeg := fun w hw hw0 => absurd ((Submodule.mem_bot (ZMod p)).mp hw) hw0
  trIn := fun w hw => by
    rw [(Submodule.mem_bot (ZMod p)).mp hw]
    exact TrIn.zero_center _

namespace IsSpBlock

variable {W L : Submodule (ZMod p) V} {β : LinearMap.BilinForm (ZMod p) V}
  (hB : IsSpBlock H W L β)
include hB

theorem vanish_left {l : V} (hl : l ∈ L) (x : V) : β l x = 0 := by
  rw [← hB.alt.neg_eq, hB.vanish x l hl, neg_zero]

theorem flip_ne_zero {w : V} (hw : w ∈ W) (hw0 : w ≠ 0) : β.flip w ≠ 0 := by
  obtain ⟨w', -, hww'⟩ := hB.nondeg w hw hw0
  intro h0
  apply hww'
  have := LinearMap.congr_fun h0 w'
  rw [LinearMap.BilinForm.flip_apply, LinearMap.zero_apply] at this
  rw [← hB.alt.neg_eq, this, neg_zero]

theorem apply_pW (x : V) {w : V} : β x w = β (pW hB.compl x) w := by
  conv_lhs => rw [← pW_add_pL hB.compl x]
  rw [LinearMap.map_add₂, hB.vanish_left (pL_mem hB.compl x), add_zero]

end IsSpBlock

section Conj

variable {β : LinearMap.BilinForm (ZMod p) V}

theorem trIn_conj_symp {u v : V} {φ : Module.Dual (ZMod p) V} (hu : TrIn H u (β.flip u))
    (hv : TrIn H v φ) (c : ZMod p) :
    TrIn H (v + (c * β v u) • u) (φ - (c * φ u) • β.flip u) := by
  obtain ⟨huu, τ, hτ, hτx⟩ := hu.smul c
  have hconj := hv.conj hτ
  have hform : φ ∘ₗ τ.symm.toLinearMap = φ - (c * φ u) • β.flip u := by
    ext z
    change φ (τ.symm z) = _
    rw [symm_apply_of_trIn huu hτx z, map_sub, map_smul]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.BilinForm.flip_apply,
      smul_eq_mul]
    ring
  rwa [hform, hτx v, LinearMap.smul_apply, LinearMap.BilinForm.flip_apply, smul_eq_mul] at hconj

private theorem trIn_step (hβ : β.IsAlt) {u u₁ r : V} {ρ : Module.Dual (ZMod p) V}
    (hgood : TrIn H (u - u₁) (β.flip (u - u₁))) (hru : β r u = 0) (hru₁ : β r u₁ = 0)
    (hρu : ρ u = 0) (hρu₁ : ρ u₁ = 0) (hu₁u : β u₁ u ≠ 0)
    (h₁ : TrIn H (u₁ + r) (β.flip u₁ + ρ)) : TrIn H (u + r) (β.flip u + ρ) := by
  have h := trIn_conj_symp hgood h₁ (β u₁ u)⁻¹
  have hβ1 : β (u₁ + r) (u - u₁) = β u₁ u := by
    simp only [LinearMap.map_add₂, map_sub, hβ.self_eq_zero, hru, hru₁, sub_zero, add_zero]
  have hβ2 : (β.flip u₁ + ρ) (u - u₁) = -β u₁ u := by
    simp only [LinearMap.add_apply, LinearMap.BilinForm.flip_apply, map_sub, hρu, hρu₁,
      hβ.self_eq_zero, sub_zero, add_zero]
    exact (hβ.neg_eq u₁ u).symm
  have hcen : u₁ + r + ((β u₁ u)⁻¹ * β (u₁ + r) (u - u₁)) • (u - u₁) = u + r := by
    rw [hβ1, inv_mul_cancel₀ hu₁u, one_smul]
    abel
  have hm : (β u₁ u)⁻¹ * -β u₁ u = -1 := by rw [mul_neg, inv_mul_cancel₀ hu₁u]
  have hax : β.flip u₁ + ρ - ((β u₁ u)⁻¹ * (β.flip u₁ + ρ) (u - u₁)) • β.flip (u - u₁) =
      β.flip u + ρ := by
    rw [hβ2, hm]
    ext z
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.BilinForm.flip_apply, map_sub, smul_eq_mul]
    ring
  rwa [hcen, hax] at h

theorem trIn_transitive (hβ : β.IsAlt) {W₀ : Submodule (ZMod p) V}
    (hnd : ∀ u ∈ W₀, u ≠ 0 → ∃ u' ∈ W₀, β u u' ≠ 0)
    (hgood : ∀ u ∈ W₀, TrIn H u (β.flip u))
    {r : V} (hr : ∀ u ∈ W₀, β u r = 0) {ρ : Module.Dual (ZMod p) V} (hρ : ∀ u ∈ W₀, ρ u = 0)
    {u₀ : V} (hu₀ : u₀ ∈ W₀) (hu₀0 : u₀ ≠ 0) (h₀ : TrIn H (u₀ + r) (β.flip u₀ + ρ)) :
    ∀ u ∈ W₀, u ≠ 0 → TrIn H (u + r) (β.flip u + ρ) := by
  have hr' : ∀ u ∈ W₀, β r u = 0 := fun u hu => by rw [← hβ.neg_eq, hr u hu, neg_zero]
  have step : ∀ u₁ ∈ W₀, ∀ u ∈ W₀, β u₁ u ≠ 0 → TrIn H (u₁ + r) (β.flip u₁ + ρ) →
      TrIn H (u + r) (β.flip u + ρ) := fun u₁ hu₁ u hu hne h₁ =>
    trIn_step hβ (hgood _ (W₀.sub_mem hu hu₁)) (hr' u hu) (hr' u₁ hu₁) (hρ u hu) (hρ u₁ hu₁)
      hne h₁
  intro u hu hu0
  by_cases h1 : β u₀ u ≠ 0
  · exact step u₀ hu₀ u hu h1 h₀
  push Not at h1
  obtain ⟨w₁, hw₁, hw₁ne⟩ := hnd u₀ hu₀ hu₀0
  obtain ⟨w₁', hw₁', hw₁'ne⟩ := hnd u hu hu0
  have hw₁'u : β w₁' u ≠ 0 := by
    rw [← hβ.neg_eq]
    exact neg_ne_zero.mpr hw₁'ne
  obtain ⟨w₂, hw₂, hu₀w₂, hw₂u⟩ : ∃ w₂ ∈ W₀, β u₀ w₂ ≠ 0 ∧ β w₂ u ≠ 0 := by
    by_cases ha : β w₁ u ≠ 0
    · exact ⟨w₁, hw₁, hw₁ne, ha⟩
    push Not at ha
    by_cases hb : β u₀ w₁' ≠ 0
    · exact ⟨w₁', hw₁', hb, hw₁'u⟩
    push Not at hb
    refine ⟨w₁ + w₁', W₀.add_mem hw₁ hw₁', ?_, ?_⟩
    · rw [map_add, hb, add_zero]
      exact hw₁ne
    · rw [LinearMap.map_add₂, ha, zero_add]
      exact hw₁'u
  exact step w₂ hw₂ u hu hw₂u (step u₀ hu₀ w₂ hw₂ hu₀w₂ h₀)

theorem trIn_span_pair (hβ : β.IsAlt) {a b : V} (ha : TrIn H a (β.flip a))
    (hb : TrIn H b (β.flip b)) (hab : β a b ≠ 0) :
    ∀ x ∈ Submodule.span (ZMod p) {a, b}, TrIn H x (β.flip x) := by
  have hsmul : ∀ (x : V) (s : ZMod p), TrIn H x (β.flip x) → TrIn H (s • x) (β.flip (s • x)) :=
    fun x s hx => by
      rw [map_smul]
      exact trIn_smul_both hx s
  have hba : β b a ≠ 0 := by
    rw [← hβ.neg_eq]
    exact neg_ne_zero.mpr hab
  have hline : ∀ s : ZMod p, TrIn H (b + s • a) (β.flip (b + s • a)) := by
    intro s
    have h := trIn_conj_symp ha hb (s / β b a)
    have hc : s / β b a * (β.flip b) a = -s := by
      rw [LinearMap.BilinForm.flip_apply, ← hβ.neg_eq]
      field_simp
    have hax : β.flip b - (s / β b a * (β.flip b) a) • β.flip a = β.flip (b + s • a) := by
      rw [hc]
      ext z
      simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
        LinearMap.BilinForm.flip_apply, map_add, map_smul, smul_eq_mul]
      ring
    rwa [div_mul_cancel₀ _ hba, hax] at h
  intro x hx
  obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hx
  by_cases ht : t = 0
  · rw [ht, zero_smul, add_zero]
    exact hsmul a s ha
  · have : s • a + t • b = t • (b + (s / t) • a) := by
      rw [smul_add, smul_smul, mul_div_cancel₀ _ ht, add_comm]
    rw [this]
    exact hsmul _ t (hline _)

theorem trIn_pm (hp : p ≠ 2) (hβ : β.IsAlt) {x₁ x₂ : V} {ρ : Module.Dual (ZMod p) V}
    (h₁ : TrIn H (x₁ + x₂) (β.flip x₁ + ρ)) (h₂ : TrIn H (x₂ - x₁) (ρ - β.flip x₁))
    (h₀ : TrIn H x₁ (β.flip x₁)) (hρ₁ : ρ x₁ = 0) (hρ₂ : ρ x₂ = 0) (hβ₂₁ : β x₂ x₁ = 0) :
    TrIn H x₂ ρ := by
  obtain ⟨-, tA, htA, htAx⟩ := h₁
  obtain ⟨-, tB, htB, htBx⟩ := h₂
  obtain ⟨-, tC, htC, htCx⟩ := h₀.smul (-2)
  have hβ11 : β x₁ x₁ = 0 := hβ.self_eq_zero x₁
  refine trIn_of_smul (two_ne_zero_of_ne_two hp) ⟨by rw [LinearMap.smul_apply, hρ₂, smul_zero],
    tA * tB * tC, H.mul_mem (H.mul_mem htA htB) htC, fun z => ?_⟩
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, htCx, htBx, htAx]
  simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.BilinForm.flip_apply, smul_eq_mul, hρ₁, hρ₂, hβ₂₁, hβ11]
  module

end Conj

end CFSG.StandardType.McLaughlinOdd
