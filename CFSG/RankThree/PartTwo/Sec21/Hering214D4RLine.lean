module

public import CFSG.RankThree.PartTwo.Sec21.Hering214KGen
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214

open CFSG.Assembly (IsElemAbelian)
open scoped commutatorElement

section Line

variable {X : Type} [Group X]

@[expose] def FourFixedMoved (ε₁ ε₂ : MulAut X) : Prop :=
  ∃ W : Subgroup X, IsElemAbelian 2 W ∧ Nat.card W = 4 ∧ (∀ w ∈ W, ε₁ w = w) ∧
    (∀ w ∈ W, ε₂ w ∈ W) ∧ ∃ w ∈ W, ε₂ w ≠ w

theorem eInvFour_of_fixed_line_four {Ē : Subgroup (MulAut X)} (hE3 : IsElemAbelian 3 Ē)
    (hE9 : Nat.card Ē = 9) {ε₁ ε₂ : MulAut X} (hε₁ : ε₁ ∈ Ē) (hε₂ : ε₂ ∈ Ē) (hε₁1 : ε₁ ≠ 1)
    (hε₂₁ : ε₂ ∉ Subgroup.zpowers ε₁) (h : FourFixedMoved ε₁ ε₂) : EInvFour X Ē := by
  obtain ⟨W, hW, hW4, hfix, hnorm, hmove⟩ := h
  exact eInvFour_of_two_gens hE3 hE9 hε₁ hε₂ hε₁1 hε₂₁ hW hW4
    (fun w hw => (hfix w hw).symm ▸ hw) hnorm (Or.inr hmove)

theorem FourFixedMoved.of_autConj (α : MulAut X) {ε₁ ε₂ : MulAut X}
    (h : FourFixedMoved (α * ε₁ * α⁻¹) (α * ε₂ * α⁻¹)) : FourFixedMoved ε₁ ε₂ := by
  obtain ⟨W, hW, hW4, hfix, hnorm, w₀, hw₀, hmove⟩ := h
  have hα : ∀ (ε : MulAut X) (y : X), (α * ε * α⁻¹) (α y) = α (ε y) := fun ε y => by
    simp [MulAut.mul_apply]
  refine ⟨W.map α⁻¹.toMonoidHom, CFSG.Open.IsElemAbelian.map hW _, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective α⁻¹.injective, hW4]
  · rintro _ ⟨w, hw, rfl⟩
    have h1 := hfix w hw
    show ε₁ (α⁻¹ w) = α⁻¹ w
    apply α.injective
    have h2 := hα ε₁ (α⁻¹ w)
    simp only [MulAut.apply_inv_self] at h2
    rw [← h2, h1]
    simp
  · rintro _ ⟨w, hw, rfl⟩
    refine ⟨(α * ε₂ * α⁻¹) w, hnorm w hw, ?_⟩
    show α⁻¹ ((α * ε₂ * α⁻¹) w) = ε₂ (α⁻¹ w)
    have h2 := hα ε₂ (α⁻¹ w)
    simp only [MulAut.apply_inv_self] at h2
    rw [h2]
    simp
  · refine ⟨α⁻¹ w₀, ⟨w₀, hw₀, rfl⟩, fun hcon => hmove ?_⟩
    have h2 := hα ε₂ (α⁻¹ w₀)
    simp only [MulAut.apply_inv_self] at h2
    rw [h2]
    have : ε₂ (α⁻¹ w₀) = α⁻¹ w₀ := hcon
    rw [this]
    simp

theorem not_mem_zpowers_of_inverts {Y : Type} [Group Y] {c ε₁ ε₂ : Y}
    (hc₁ : c * ε₁ * c⁻¹ = ε₁) (hc₂ : c * ε₂ * c⁻¹ = ε₂⁻¹) (h3 : ε₂ ^ 3 = 1) (h1 : ε₂ ≠ 1) :
    ε₂ ∉ Subgroup.zpowers ε₁ := by
  rintro ⟨k, hk⟩
  have hfix : c * ε₂ * c⁻¹ = ε₂ := by
    rw [← hk]
    have : c * ε₁ ^ k * c⁻¹ = (c * ε₁ * c⁻¹) ^ k := by
      rw [← MulAut.conj_apply, ← MulAut.conj_apply, map_zpow]
    rw [this, hc₁]
  rw [hfix] at hc₂
  apply h1
  have h2 : ε₂ * ε₂ = 1 := by
    have := congrArg (fun y => ε₂ * y) hc₂
    simpa using this
  calc ε₂ = ε₂ ^ 3 * (ε₂ * ε₂)⁻¹ := by group
    _ = 1 := by rw [h3, h2]; simp

theorem inv_mul_inv_of_pow_three {Y : Type} [Group Y] {a : Y} (h : a ^ 3 = 1) :
    a⁻¹ * a⁻¹ = a := by
  have h2 : a * a * a = 1 := by rw [← pow_three']; exact h
  calc a⁻¹ * a⁻¹ = (a * a * a)⁻¹ * a := by group
    _ = a := by rw [h2]; group

theorem commutator_eq_of_inverts {Y : Type} [Group Y] {x g : Y} (hx : x * g * x⁻¹ = g⁻¹)
    (hg : g ^ 3 = 1) : ⁅x, g⁆ = g := by
  rw [commutatorElement_def, hx]
  exact inv_mul_inv_of_pow_three hg

@[expose] def NormMoveFour {K : Type*} [Group K] (h : K) : Prop :=
  ∃ W : Subgroup K, IsElemAbelian 2 W ∧ Nat.card W = 4 ∧ (∀ w ∈ W, h * w * h⁻¹ ∈ W) ∧
    ∃ w ∈ W, h * w * h⁻¹ ≠ w

theorem NormMoveFour.map_injective {K L : Type*} [Group K] [Group L] (f : K →* L)
    (hf : Function.Injective f) {h : K} (H : NormMoveFour h) : NormMoveFour (f h) := by
  obtain ⟨W, hW, hW4, hnorm, w₀, hw₀, hmove⟩ := H
  refine ⟨W.map f, CFSG.Open.IsElemAbelian.map hW f, ?_, ?_, f w₀, ⟨w₀, hw₀, rfl⟩, ?_⟩
  · rw [Subgroup.card_map_of_injective hf, hW4]
  · rintro _ ⟨w, hw, rfl⟩
    exact ⟨h * w * h⁻¹, hnorm w hw, by simp⟩
  · intro hc
    apply hmove
    apply hf
    simpa using hc

theorem NormMoveFour.of_conj {K : Type*} [Group K] (y h : K) (H : NormMoveFour (y * h * y⁻¹)) :
    NormMoveFour h := by
  have := NormMoveFour.map_injective (MulAut.conj y⁻¹).toMonoidHom (MulAut.conj y⁻¹).injective H
  have e : (MulAut.conj y⁻¹).toMonoidHom (y * h * y⁻¹) = h := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rwa [e] at this

theorem NormMoveFour.of_mulEquiv {K L : Type*} [Group K] [Group L] (e : K ≃* L) {h : K}
    (H : NormMoveFour (e h)) : NormMoveFour h := by
  have := NormMoveFour.map_injective e.symm.toMonoidHom e.symm.injective H
  simpa using this

theorem fourFixedMoved_of_subgroup {X : Type} [Group X] {S : Subgroup X} {β : MulAut X}
    (hS : ∀ s ∈ S, β s = s) {g : X} (hg : g ∈ S) (H : NormMoveFour (⟨g, hg⟩ : S)) :
    FourFixedMoved β (MulAut.conj g) := by
  obtain ⟨W, hW, hW4, hnorm, w₀, hw₀, hmove⟩ := H
  refine ⟨W.map S.subtype, CFSG.Open.IsElemAbelian.map hW _, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective S.subtype_injective, hW4]
  · rintro _ ⟨w, hw, rfl⟩
    exact hS w w.2
  · rintro _ ⟨w, hw, rfl⟩
    exact ⟨⟨g, hg⟩ * w * ⟨g, hg⟩⁻¹, hnorm w hw, by simp [MulAut.conj_apply]⟩
  · refine ⟨S.subtype w₀, ⟨w₀, hw₀, rfl⟩, fun hc => hmove ?_⟩
    apply Subtype.ext
    simpa [MulAut.conj_apply] using hc

theorem EInvFour.of_map_mulEquiv {Y : Type} [Group Y] (e : X ≃* Y) {Ē : Subgroup (MulAut X)}
    (h : EInvFour Y (Ē.map (MulAut.congr e).toMonoidHom)) : EInvFour X Ē := by
  obtain ⟨W, hW, hW4, hinv, σ', hσ', w, hw, hne⟩ := h
  refine ⟨W.map e.symm.toMonoidHom, CFSG.Open.IsElemAbelian.map hW _, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective e.symm.injective, hW4]
  · intro σ hσ x hx
    obtain ⟨w', hw', rfl⟩ := hx
    refine ⟨MulAut.congr e σ w', hinv _ ⟨σ, hσ, rfl⟩ _ hw', ?_⟩
    simp [MulAut.congr_apply]
  · obtain ⟨σ, hσ, rfl⟩ := hσ'
    refine ⟨σ, hσ, e.symm w, ⟨w, hw, rfl⟩, fun h => hne ?_⟩
    have h1 := congrArg e h
    simpa [MulAut.congr_apply] using h1

end Line

end CFSG.RankThree.PartTwo.Sec21.Hering214
