module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Solvable

public section

namespace CFSG.RankThree.PartTwo.Sec15

@[expose] def Res1AutSolv (Y : Type) [Group Y] : Prop :=
  ∀ y : Y, orderOf y = 3 → ∀ V : Subgroup (MulAut Y), (∀ α ∈ V, α y = y) → Group.IsSolvable V

@[expose] def Res1AutFix (Y : Type) [Group Y] : Prop :=
  ∀ y : Y, orderOf y = 3 → ∀ R₀ : Subgroup Y, R₀ ≠ ⊥ → IsPGroup 2 R₀ →
    (∀ r ∈ R₀, y * r * y⁻¹ ∈ R₀) → ∀ X : Subgroup (MulAut Y), IsPGroup 2 X →
      (∀ α ∈ X, α y = y) → (∀ α ∈ X, ∀ r ∈ R₀, α r ∈ R₀) → X = ⊥

theorem Res1AutSolv.of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : Res1AutSolv Y') : Res1AutSolv Y := by
  intro y hy V hV
  set Φ := MulAut.congr e
  have hs := h (e y) (by rw [MulEquiv.orderOf_eq]; exact hy) (V.map Φ.toMonoidHom)
    (by
      rintro _ ⟨α, hα, rfl⟩
      simp [Φ, hV α hα])
  haveI := hs
  let ψ := V.equivMapOfInjective Φ.toMonoidHom Φ.injective
  exact solvable_of_solvable_injective (f := ψ.toMonoidHom) ψ.injective

theorem Res1AutFix.of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : Res1AutFix Y') : Res1AutFix Y := by
  intro y hy R₀ hR₀ hR₂ hyR X hX hXy hXR
  set Φ := MulAut.congr e
  have hbot := h (e y) (by rw [MulEquiv.orderOf_eq]; exact hy) (R₀.map e.toMonoidHom)
    (by
      intro hb
      apply hR₀
      rw [eq_bot_iff]
      intro r hr
      have : e r ∈ R₀.map e.toMonoidHom := ⟨r, hr, rfl⟩
      rw [hb, Subgroup.mem_bot] at this
      simpa using this)
    (hR₂.map e.toMonoidHom)
    (by
      rintro _ ⟨r, hr, rfl⟩
      exact ⟨y * r * y⁻¹, hyR r hr, by simp⟩)
    (X.map Φ.toMonoidHom) (hX.map Φ.toMonoidHom)
    (by
      rintro _ ⟨α, hα, rfl⟩
      simp [Φ, hXy α hα])
    (by
      rintro _ ⟨α, hα, rfl⟩ _ ⟨r, hr, rfl⟩
      exact ⟨α r, hXR α hα r hr, by simp [Φ]⟩)
  rw [eq_bot_iff]
  intro α hα
  have : Φ α ∈ X.map Φ.toMonoidHom := ⟨α, hα, rfl⟩
  rw [hbot, Subgroup.mem_bot] at this
  rw [Subgroup.mem_bot]
  exact Φ.injective (by simpa using this)

end CFSG.RankThree.PartTwo.Sec15
