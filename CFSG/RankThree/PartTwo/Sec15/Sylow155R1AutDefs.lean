module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.RankThree.PartTwo.Sec15

@[expose] def Res1AutCent (Y : Type) [Group Y] : Prop :=
  ∀ (α : MulAut Y) (V : Subgroup (MulAut Y)) (y : Y), orderOf y = 3 →
    Nat.Coprime (orderOf α) 6 → α y = y → IsPGroup 2 V →
    (∀ v ∈ V, α * v * α⁻¹ ∈ V) → (∀ v ∈ V, MulAut.conj y * v * (MulAut.conj y)⁻¹ ∈ V) →
      ∀ v ∈ V, α * v = v * α

theorem Res1AutCent.of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : Res1AutCent Y') : Res1AutCent Y := by
  intro α V y hy hα hαy hV hαV hyV v hv
  set Φ := MulAut.congr e
  have hconj : MulAut.conj (e y) = Φ (MulAut.conj y) := by
    ext z
    simp [Φ, MulAut.conj_apply]
  have hΦα : Φ α (e y) = e y := by simp [Φ, hαy]
  have key := h (Φ α) (V.map Φ.toMonoidHom) (e y) (by rw [MulEquiv.orderOf_eq]; exact hy)
    (by rw [MulEquiv.orderOf_eq]; exact hα) hΦα (hV.map Φ.toMonoidHom)
    (by
      rintro _ ⟨w, hw, rfl⟩
      exact ⟨α * w * α⁻¹, hαV w hw, by simp⟩)
    (by
      rintro _ ⟨w, hw, rfl⟩
      refine ⟨MulAut.conj y * w * (MulAut.conj y)⁻¹, hyV w hw, ?_⟩
      simp [hconj])
    (Φ v) ⟨v, hv, rfl⟩
  apply Φ.injective
  simpa using key

end CFSG.RankThree.PartTwo.Sec15
