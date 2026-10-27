module

public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Group

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

@[expose] def s16c13bcA_PairFixed (Γ W : Type*) [Group Γ] [MulAction Γ W] : Prop :=
  ∀ w : W, ∃ g₁ g₂ : Γ, orderOf g₁ = 3 ∧ orderOf g₂ = 3 ∧ g₁ * g₂ = g₂ * g₁ ∧
    g₂ ∉ Subgroup.zpowers g₁ ∧ g₁ • w = w ∧ g₂ • w = w

@[expose] def s16c13bcA_PairFix {W : Type} [CommGroup W] (H : Subgroup (MulAut W))
    (J : Subgroup W) : Prop :=
  ∀ w ∈ J, w ≠ 1 → ∃ a ∈ H, ∃ b ∈ H, orderOf a = 3 ∧ orderOf b = 3 ∧ a * b = b * a ∧
    b ∉ Subgroup.zpowers a ∧ a w = w ∧ b w = w

theorem s16c13bcA_pair_conj {Γ : Type*} [Group Γ] {g₁ g₂ : Γ} (h₁ : orderOf g₁ = 3)
    (h₂ : orderOf g₂ = 3) (hc : g₁ * g₂ = g₂ * g₁) (hn : g₂ ∉ Subgroup.zpowers g₁) (c : Γ) :
    orderOf (c * g₁ * c⁻¹) = 3 ∧ orderOf (c * g₂ * c⁻¹) = 3 ∧
      c * g₁ * c⁻¹ * (c * g₂ * c⁻¹) = c * g₂ * c⁻¹ * (c * g₁ * c⁻¹) ∧
      c * g₂ * c⁻¹ ∉ Subgroup.zpowers (c * g₁ * c⁻¹) := by
  have hord : ∀ g : Γ, orderOf (c * g * c⁻¹) = orderOf g := fun g => by
    have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective g
    simpa [MulAut.conj_apply] using this
  refine ⟨(hord g₁).trans h₁, (hord g₂).trans h₂, ?_, ?_⟩
  · calc c * g₁ * c⁻¹ * (c * g₂ * c⁻¹) = c * (g₁ * g₂) * c⁻¹ := by group
      _ = c * (g₂ * g₁) * c⁻¹ := by rw [hc]
      _ = c * g₂ * c⁻¹ * (c * g₁ * c⁻¹) := by group
  · intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
    apply hn
    refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
    have h1 : c * g₁ ^ k * c⁻¹ = c * g₂ * c⁻¹ := by rw [← hk, conj_zpow]
    have h2 : g₁ ^ k = g₂ := by
      have := mul_left_cancel (mul_right_cancel h1)
      exact this
    exact h2

theorem s16c13bcA_pairFixed_of_orbit {Γ W : Type*} [Group Γ] [MulAction Γ W] {e v : W} {c : Γ}
    (hcv : c • e = v)
    (he : ∃ g₁ g₂ : Γ, orderOf g₁ = 3 ∧ orderOf g₂ = 3 ∧ g₁ * g₂ = g₂ * g₁ ∧
      g₂ ∉ Subgroup.zpowers g₁ ∧ g₁ • e = e ∧ g₂ • e = e) :
    ∃ g₁ g₂ : Γ, orderOf g₁ = 3 ∧ orderOf g₂ = 3 ∧ g₁ * g₂ = g₂ * g₁ ∧
      g₂ ∉ Subgroup.zpowers g₁ ∧ g₁ • v = v ∧ g₂ • v = v := by
  obtain ⟨g₁, g₂, h₁, h₂, hc, hn, hg₁, hg₂⟩ := he
  obtain ⟨o₁, o₂, hcomm, hnot⟩ := s16c13bcA_pair_conj h₁ h₂ hc hn c
  refine ⟨c * g₁ * c⁻¹, c * g₂ * c⁻¹, o₁, o₂, hcomm, hnot, ?_, ?_⟩
  · rw [← hcv, mul_smul, mul_smul, inv_smul_smul, hg₁]
  · rw [← hcv, mul_smul, mul_smul, inv_smul_smul, hg₂]

theorem s16c13bcA_pairFix_twist {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {J : Subgroup W} (h : s16c13bcA_PairFix H J) {κ : MulAut W}
    (hκ : ∀ l ∈ H, κ * l = l * κ) : s16c13bcA_PairFix H (J.map κ.toMonoidHom) := by
  rintro w ⟨u, hu, rfl⟩ hw1
  have hu1 : u ≠ 1 := fun h1 => hw1 (by rw [h1]; exact map_one _)
  obtain ⟨a, ha, b, hb, ha3, hb3, hab, hn, hau, hbu⟩ := h u hu hu1
  refine ⟨a, ha, b, hb, ha3, hb3, hab, hn, ?_, ?_⟩
  · show a (κ u) = κ u
    calc a (κ u) = (a * κ) u := rfl
      _ = (κ * a) u := by rw [← hκ a ha]
      _ = κ (a u) := rfl
      _ = κ u := by rw [hau]
  · show b (κ u) = κ u
    calc b (κ u) = (b * κ) u := rfl
      _ = (κ * b) u := by rw [← hκ b hb]
      _ = κ (b u) := rfl
      _ = κ u := by rw [hbu]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
