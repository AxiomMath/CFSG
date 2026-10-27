module

public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalEvenLinearSource
public import CFSG.LinearAlgebra.LinearGroups.Generation

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleCommParts

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped commutatorElement

theorem model3LinGen_ut_mem {F' : Type} [Field F'] (Y₁ : Subgroup (SpecialLinearGroup (Fin 3) F'))
    (hUT : unitriangular 3 F' ≤ Y₁) {i j : Fin 3} (hij : i < j) (c : F') :
    SpecialLinearGroup.transvection (ne_of_lt hij) c ∈ Y₁ := by
  have h := hUT (CFSG.ComponentClassification.SymmetricLocal.utTransvection hij c).2
  have e : ((CFSG.ComponentClassification.SymmetricLocal.utTransvection hij c :
      unitriangular 3 F') : SpecialLinearGroup (Fin 3) F') =
      SpecialLinearGroup.transvection (ne_of_lt hij) c := by
    apply Subtype.ext
    exact CFSG.ComponentClassification.SymmetricLocal.coe_utTransvection hij c
  rw [e] at h
  exact h

theorem model3LinGen_comm_mem {F' : Type} [Field F'] (Y₁ : Subgroup (SpecialLinearGroup (Fin 3) F'))
    {g h : SpecialLinearGroup (Fin 3) F'} (hg : g ∈ Y₁) (hh : h ∈ Y₁) : ⁅g, h⁆ ∈ Y₁ := by
  rw [commutatorElement_def]
  exact Y₁.mul_mem (Y₁.mul_mem (Y₁.mul_mem hg hh) (Y₁.inv_mem hg)) (Y₁.inv_mem hh)

theorem model3_linear_generation {F' : Type} [Field F']
    (Y₁ : Subgroup (SpecialLinearGroup (Fin 3) F')) (hUT : unitriangular 3 F' ≤ Y₁)
    (h31 : ∀ (A : SpecialLinearGroup (Fin 3) F') (c : F'),
      (A : Matrix (Fin 3) (Fin 3) F') = transvection 2 0 c → A ∈ Y₁) : Y₁ = ⊤ := by
  have hgen := CFSG.LinearGroups.special_linear_elementary_generation (n := 3) (K := F')
  rw [eq_top_iff, ← hgen, Subgroup.closure_le]
  rintro A ⟨i, j, hij, c, rfl⟩
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact model3LinGen_ut_mem Y₁ hUT (by decide) c
  · exact model3LinGen_ut_mem Y₁ hUT (by decide) c
  ·
    have hA := model3LinGen_ut_mem Y₁ hUT (show (1 : Fin 3) < 2 by decide) (1 : F')
    have hB := h31 (SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) c) c rfl
    have key := SpecialLinearGroup.commutatorElement_transvection
      (show (1 : Fin 3) ≠ 2 by decide) (show (2 : Fin 3) ≠ 0 by decide) hij (1 : F') c
    rw [_root_.one_mul] at key
    rw [← key]
    exact model3LinGen_comm_mem Y₁ hA hB
  · exact absurd rfl hij
  · exact model3LinGen_ut_mem Y₁ hUT (by decide) c
  · exact h31 (SpecialLinearGroup.transvection hij c) c rfl
  ·
    have hA := h31 (SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) c) c rfl
    have hB := model3LinGen_ut_mem Y₁ hUT (show (0 : Fin 3) < 1 by decide) (1 : F')
    have key := SpecialLinearGroup.commutatorElement_transvection
      (show (2 : Fin 3) ≠ 0 by decide) (show (0 : Fin 3) ≠ 1 by decide) hij c (1 : F')
    rw [_root_.mul_one] at key
    rw [← key]
    exact model3LinGen_comm_mem Y₁ hA hB
  · exact absurd rfl hij

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard
