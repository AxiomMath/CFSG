module

import Mathlib.Data.Nat.Choose.Dvd
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Defs
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.RankThree.PartOne.LIT

section Flag

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

@[expose] def flagGroup (D₁ D₂ : Submodule K V) (h12 : D₁ ≤ D₂) : Subgroup (V ≃ₗ[K] V) where
  carrier := {g | (∀ x, g x - x ∈ D₂) ∧ (∀ x ∈ D₂, g x - x ∈ D₁) ∧ (∀ x ∈ D₁, g x = x)}
  one_mem' := ⟨fun x => by simp, fun x _ => by simp, fun x _ => rfl⟩
  mul_mem' := by
    rintro g g' ⟨hg1, hg2, hg3⟩ ⟨hg1', hg2', hg3'⟩
    have hgD₂ : ∀ y ∈ D₂, g y ∈ D₂ := fun y hy => by
      have := D₂.add_mem hy (h12 (hg2 y hy))
      simpa using this
    refine ⟨fun x => ?_, fun x hx => ?_, fun x hx => ?_⟩
    · have : (g * g') x - x = g (g' x - x) + (g x - x) := by
        simp only [LinearEquiv.mul_apply, map_sub]; abel
      rw [this]
      exact D₂.add_mem (hgD₂ _ (hg1' x)) (hg1 x)
    · have : (g * g') x - x = (g' x - x) + (g x - x) := by
        have h1 : g (g' x - x) = g' x - x := hg3 _ (hg2' x hx)
        have : (g * g') x - x = g (g' x - x) + (g x - x) := by
          simp only [LinearEquiv.mul_apply, map_sub]; abel
        rw [this, h1]
      rw [this]
      exact D₁.add_mem (hg2' x hx) (hg2 x hx)
    · rw [LinearEquiv.mul_apply, hg3' x hx, hg3 x hx]
  inv_mem' := by
    rintro g ⟨hg1, hg2, hg3⟩
    have hinvD₂ : ∀ y ∈ D₂, g⁻¹ y ∈ D₂ := fun y hy => by
      have h := hg1 (g.symm y)
      have : g (g.symm y) = y := by simp
      rw [this] at h
      have := D₂.sub_mem hy h
      simpa using this
    have hinvD₁ : ∀ y ∈ D₁, g⁻¹ y = y := fun y hy => by
      have : g y = y := hg3 y hy
      show g.symm y = y
      rw [LinearEquiv.symm_apply_eq]
      exact this.symm
    refine ⟨fun x => ?_, fun x hx => ?_, fun x hx => hinvD₁ x hx⟩
    · have h := hg1 (g.symm x)
      have e : g (g.symm x) = x := by simp
      rw [e] at h
      have := D₂.neg_mem h
      show g.symm x - x ∈ D₂
      simpa using this
    · have hz : g.symm x ∈ D₂ := hinvD₂ x hx
      have h := hg2 _ hz
      have e : g (g.symm x) = x := by simp
      rw [e] at h
      have := D₁.neg_mem h
      show g.symm x - x ∈ D₁
      simpa using this

theorem mem_flagGroup {D₁ D₂ : Submodule K V} {h12 : D₁ ≤ D₂} {g : V ≃ₗ[K] V} :
    g ∈ flagGroup D₁ D₂ h12 ↔
      (∀ x, g x - x ∈ D₂) ∧ (∀ x ∈ D₂, g x - x ∈ D₁) ∧ (∀ x ∈ D₁, g x = x) :=
  Iff.rfl

theorem conj_mem_flagGroup {D₁ D₂ : Submodule K V} (h12 : D₁ ≤ D₂) {g : V ≃ₗ[K] V}
    (hg₁ : ∀ x ∈ D₁, g x ∈ D₁) (hg₂ : ∀ x ∈ D₂, g x ∈ D₂)
    (hgi₁ : ∀ x ∈ D₁, g⁻¹ x ∈ D₁) (hgi₂ : ∀ x ∈ D₂, g⁻¹ x ∈ D₂)
    {r : V ≃ₗ[K] V} (hr : r ∈ flagGroup D₁ D₂ h12) : g * r * g⁻¹ ∈ flagGroup D₁ D₂ h12 := by
  obtain ⟨hr1, hr2, hr3⟩ := hr
  refine ⟨fun x => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · have : (g * r * g⁻¹) x - x = g (r (g⁻¹ x) - g⁻¹ x) := by
      simp only [LinearEquiv.mul_apply, map_sub]
      have : g (g⁻¹ x) = x := by simp
      rw [this]
    rw [this]
    exact hg₂ _ (hr1 _)
  · have : (g * r * g⁻¹) x - x = g (r (g⁻¹ x) - g⁻¹ x) := by
      simp only [LinearEquiv.mul_apply, map_sub]
      have : g (g⁻¹ x) = x := by simp
      rw [this]
    rw [this]
    exact hg₁ _ (hr2 _ (hgi₂ x hx))
  · have h1 := hr3 _ (hgi₁ x hx)
    simp only [LinearEquiv.mul_apply]
    rw [h1]
    simp

theorem pow_apply_of_two (g : V ≃ₗ[K] V) (y : V) (hy : g (g y - y) = g y - y) (n : ℕ) :
    (g ^ n) y = y + (n : K) • (g y - y) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', LinearEquiv.mul_apply, ih, map_add, map_smul, hy]
    push_cast
    module

theorem pow_apply_of_three (g : V ≃ₗ[K] V) (x : V)
    (hb : g (g (g x - x) - (g x - x)) = g (g x - x) - (g x - x)) (n : ℕ) :
    (g ^ n) x = x + (n : K) • (g x - x) +
      ((n.choose 2 : ℕ) : K) • (g (g x - x) - (g x - x)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : (g ^ (n + 1)) x = (g ^ n) x + (g ^ n) (g x - x) := by
      rw [pow_succ, LinearEquiv.mul_apply]
      have : g x = x + (g x - x) := by abel
      conv_lhs => rw [this]
      rw [map_add]
    rw [e, ih, pow_apply_of_two g (g x - x) (by
      have := hb
      simpa using this) n]
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    push_cast
    module

end Flag

section Prime

variable {p : ℕ} [Fact p.Prime] {W : Type*} [AddCommGroup W] [Module (ZMod p) W]

theorem pow_prime_of_three (hp : 3 ≤ p) (g : W ≃ₗ[ZMod p] W) (x : W)
    (hb : g (g (g x - x) - (g x - x)) = g (g x - x) - (g x - x)) :
    (g ^ p) x = x := by
  have h := pow_apply_of_three g x hb p
  have h1 : ((p : ℕ) : ZMod p) = 0 := ZMod.natCast_self p
  have h2 : ((p.choose 2 : ℕ) : ZMod p) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    exact (Fact.out : p.Prime).dvd_choose_self (by norm_num) (by omega)
  rw [h1, h2] at h
  simpa using h

theorem flagGroup_pow_prime (hp : 3 ≤ p) {D₁ D₂ : Submodule (ZMod p) W} (h12 : D₁ ≤ D₂)
    {g : W ≃ₗ[ZMod p] W} (hg : g ∈ flagGroup D₁ D₂ h12) : g ^ p = 1 := by
  obtain ⟨hg1, hg2, hg3⟩ := hg
  ext x
  have hb : g (g (g x - x) - (g x - x)) = g (g x - x) - (g x - x) :=
    hg3 _ (hg2 _ (hg1 x))
  rw [pow_prime_of_three hp g x hb]
  rfl

theorem flag_comm (hp : 3 ≤ p) (Γ Λ : Subgroup (W ≃ₗ[ZMod p] W)) (hΛΓ : Λ ≤ Γ) (v : W)
    (hnorm : ∀ g ∈ Γ, g v ∈ Submodule.span (ZMod p) {v} → ∀ l ∈ Λ, g * l * g⁻¹ ∈ Λ)
    (hfix : ∀ l ∈ Λ, l v = v) (hO : CFSG.pCore p Λ = ⊥)
    (D₁ D₂ : Submodule (ZMod p) W) (h12 : D₁ ≤ D₂) (hv : v ∈ D₁)
    (hD₁ : ∀ g ∈ Γ, g v ∈ Submodule.span (ZMod p) {v} → ∀ x ∈ D₁, g x ∈ D₁)
    (hD₂ : ∀ g ∈ Γ, g v ∈ Submodule.span (ZMod p) {v} → ∀ x ∈ D₂, g x ∈ D₂)
    {r : W ≃ₗ[ZMod p] W} (hr : r ∈ Γ) (hrf : r ∈ flagGroup D₁ D₂ h12)
    {l : W ≃ₗ[ZMod p] W} (hl : l ∈ Λ) : l * r = r * l := by
  have hΛs : ∀ g ∈ Λ, g v ∈ Submodule.span (ZMod p) {v} := fun g hg => by
    rw [hfix g hg]; exact Submodule.subset_span rfl
  have hcon : ∀ g ∈ Λ, ∀ s ∈ flagGroup D₁ D₂ h12, g * s * g⁻¹ ∈ flagGroup D₁ D₂ h12 := by
    intro g hg s hs
    exact conj_mem_flagGroup h12 (hD₁ g (hΛΓ hg) (hΛs g hg)) (hD₂ g (hΛΓ hg) (hΛs g hg))
      (hD₁ g⁻¹ (hΛΓ (Λ.inv_mem hg)) (hΛs g⁻¹ (Λ.inv_mem hg)))
      (hD₂ g⁻¹ (hΛΓ (Λ.inv_mem hg)) (hΛs g⁻¹ (Λ.inv_mem hg))) hs
  let N : Subgroup Λ := (flagGroup D₁ D₂ h12).subgroupOf Λ
  have hNn : N.Normal := ⟨fun n hn g => hcon g g.2 n hn⟩
  have hNp : IsPGroup p N := by
    rw [IsPGroup.iff_orderOf]
    intro g
    have h1 : ((g : Λ) : W ≃ₗ[ZMod p] W) ^ p = 1 := flagGroup_pow_prime hp h12 g.2
    have h2 : g ^ p = 1 := Subtype.ext (Subtype.ext h1)
    have h3 : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one h2
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp h3 with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  have hNle : N ≤ CFSG.pCore p Λ := le_sSup ⟨hNn, hNp⟩
  have hN1 : ∀ n ∈ N, n = 1 := fun n hn => by
    have := hNle hn
    rw [hO, Subgroup.mem_bot] at this
    exact this
  have hlinv : l⁻¹ ∈ Λ := Λ.inv_mem hl
  have hrv : r v = v := hrf.2.2 v hv
  have hrs : r v ∈ Submodule.span (ZMod p) {v} := by rw [hrv]; exact Submodule.subset_span rfl
  have hc1 : r * l⁻¹ * r⁻¹ ∈ Λ := hnorm r hr hrs l⁻¹ hlinv
  have hcΛ : l * r * l⁻¹ * r⁻¹ ∈ Λ := by
    have := Λ.mul_mem hl hc1
    simpa [mul_assoc] using this
  have hcf : l * r * l⁻¹ * r⁻¹ ∈ flagGroup D₁ D₂ h12 :=
    (flagGroup D₁ D₂ h12).mul_mem (hcon l hl r hrf) ((flagGroup D₁ D₂ h12).inv_mem hrf)
  have hcN : (⟨l * r * l⁻¹ * r⁻¹, hcΛ⟩ : Λ) ∈ N := hcf
  have h1 := hN1 _ hcN
  have h2 : l * r * l⁻¹ * r⁻¹ = 1 := congrArg Subtype.val h1
  exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h2)

end Prime

end CFSG.RankThree.PartOne.LIT
