module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import CFSG.RankThree.PartOne.AUTSL.Interface

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem s16t3_twist_of_isomorphisms {n : ℕ} (hn : 3 ≤ n) {H : Type*} [Group H]
    {π₁ π₂ : Matrix.SpecialLinearGroup (Fin n) (ZMod 2) →* H}
    (hi₁ : Function.Injective π₁) (hs₁ : Function.Surjective π₁)
    (hi₂ : Function.Injective π₂) (hs₂ : Function.Surjective π₂) :
    ∃ A : Matrix.GeneralLinearGroup (Fin n) (ZMod 2),
      (∀ s : Matrix.SpecialLinearGroup (Fin n) (ZMod 2),
        ∃ t : Matrix.SpecialLinearGroup (Fin n) (ZMod 2), π₂ t = π₁ s ∧
          (t : Matrix (Fin n) (Fin n) (ZMod 2)) = (A : Matrix (Fin n) (Fin n) (ZMod 2)) *
            (s : Matrix (Fin n) (Fin n) (ZMod 2)) *
              ((A⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
                Matrix (Fin n) (Fin n) (ZMod 2))) ∨
      (∀ s : Matrix.SpecialLinearGroup (Fin n) (ZMod 2),
        ∃ t : Matrix.SpecialLinearGroup (Fin n) (ZMod 2), π₂ t = π₁ s ∧
          (t : Matrix (Fin n) (Fin n) (ZMod 2)) = (A : Matrix (Fin n) (Fin n) (ZMod 2)) *
            ((s⁻¹ : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
              Matrix (Fin n) (Fin n) (ZMod 2)).transpose *
              ((A⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
                Matrix (Fin n) (Fin n) (ZMod 2))) := by
  classical
  let e₁ : Matrix.SpecialLinearGroup (Fin n) (ZMod 2) ≃* H :=
    MulEquiv.ofBijective π₁ ⟨hi₁, hs₁⟩
  let e₂ : Matrix.SpecialLinearGroup (Fin n) (ZMod 2) ≃* H :=
    MulEquiv.ofBijective π₂ ⟨hi₂, hs₂⟩
  let ψ : MulAut (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := e₁.trans e₂.symm
  obtain ⟨A, σ, h | h⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_matrix_form_of_mulAut_sl hn ψ
  · refine ⟨A, Or.inl ?_⟩
    intro s
    refine ⟨ψ s, ?_, ?_⟩
    · change e₂ (e₂.symm (e₁ s)) = e₁ s
      exact e₂.apply_symm_apply _
    · have hσ : ∀ x : ZMod 2, σ x = x := fun x => by
        fin_cases x
        · exact σ.map_zero
        · exact σ.map_one
      have hmap : ∀ M : Matrix (Fin n) (Fin n) (ZMod 2), M.map σ = M := by
        intro M
        ext i j
        simp [hσ]
      have hs := h s
      rw [hmap] at hs
      exact hs
  · refine ⟨A, Or.inr ?_⟩
    intro s
    refine ⟨ψ s, ?_, ?_⟩
    · change e₂ (e₂.symm (e₁ s)) = e₁ s
      exact e₂.apply_symm_apply _
    · have hσ : ∀ x : ZMod 2, σ x = x := fun x => by
        fin_cases x
        · exact σ.map_zero
        · exact σ.map_one
      have hmap : ∀ M : Matrix (Fin n) (Fin n) (ZMod 2), M.map σ = M := by
        intro M
        ext i j
        simp [hσ]
      have hs := h s
      rw [hmap] at hs
      exact hs

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
