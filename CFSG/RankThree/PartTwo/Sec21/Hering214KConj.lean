module

import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.RankThree.PartTwo.Sec21.Hering214Reduce

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214

open CFSG.Assembly (IsElemAbelian)

variable {C : Type} [Group C]

theorem eInvFour_of_conj_data {Ē : Subgroup (MulAut C)}
    (hrange : Ē ≤ (MulAut.conj : C →* MulAut C).range) (g : C) {W : Subgroup C}
    (hW : IsElemAbelian 2 W) (hW4 : Nat.card W = 4)
    (hinv : ∀ x : C, MulAut.conj x ∈ Ē → ∀ w ∈ W,
      (g * x * g⁻¹) * w * (g * x * g⁻¹)⁻¹ ∈ W)
    (hmove : ∃ x : C, MulAut.conj x ∈ Ē ∧ ∃ w ∈ W,
      (g * x * g⁻¹) * w * (g * x * g⁻¹)⁻¹ ≠ w) : EInvFour C Ē := by
  set W' : Subgroup C := W.map (MulAut.conj g⁻¹).toMonoidHom with hW'
  have hmem : ∀ v, v ∈ W' ↔ ∃ w ∈ W, g⁻¹ * w * g = v := by
    intro v
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, by simp [MulAut.conj_apply]⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, by simp [MulAut.conj_apply]⟩
  refine ⟨W', CFSG.Open.IsElemAbelian.map hW _, ?_, ?_, ?_⟩
  · rw [hW', Subgroup.card_map_of_injective (show Function.Injective
      (MulAut.conj g⁻¹).toMonoidHom from (MulAut.conj g⁻¹).injective), hW4]
  · intro σ hσ v hv
    obtain ⟨w, hw, rfl⟩ := (hmem v).mp hv
    obtain ⟨x, hx⟩ := hrange hσ
    have hxE : MulAut.conj x ∈ Ē := by rw [hx]; exact hσ
    rw [← hx]
    refine (hmem _).mpr ⟨(g * x * g⁻¹) * w * (g * x * g⁻¹)⁻¹, hinv x hxE w hw, ?_⟩
    simp only [MulAut.conj_apply]
    group
  · obtain ⟨x, hxE, w, hw, hne⟩ := hmove
    refine ⟨MulAut.conj x, hxE, g⁻¹ * w * g, (hmem _).mpr ⟨w, hw, rfl⟩, fun h => hne ?_⟩
    simp only [MulAut.conj_apply] at h
    have h2 : g * (x * (g⁻¹ * w * g) * x⁻¹) * g⁻¹ = g * (g⁻¹ * w * g) * g⁻¹ := by rw [h]
    have h3 : (g * x * g⁻¹) * w * (g * x * g⁻¹)⁻¹ = w := by
      calc (g * x * g⁻¹) * w * (g * x * g⁻¹)⁻¹
          = g * (x * (g⁻¹ * w * g) * x⁻¹) * g⁻¹ := by group
        _ = g * (g⁻¹ * w * g) * g⁻¹ := h2
        _ = w := by group
    exact h3

end CFSG.RankThree.PartTwo.Sec21.Hering214
