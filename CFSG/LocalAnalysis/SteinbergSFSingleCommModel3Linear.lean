module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommModel3Conj
public import CFSG.LocalAnalysis.SteinbergSFSingleCommModel3LinearInv
public import CFSG.LocalAnalysis.SteinbergSFSingleCommModel3LinearDich
public import CFSG.LocalAnalysis.SteinbergSFSingleCommModel3LinearOpp
public import CFSG.LocalAnalysis.SteinbergSFSingleCommModel3LinearGen

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleCommParts

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Linear

variable {F' : Type} [Field F'] [Finite F'] [CharP F' 2]

theorem model3_linear_a_ut :
    Model3A (SpecialLinearGroup (Fin 3) F') (unitriangular 3 F') (Nat.card F') := by
  refine ⟨CFSG.ComponentClassification.SymmetricLocal.card_center_unitriangular (by norm_num),
    fun z hz => ?_⟩
  have hzc := CFSG.ComponentClassification.SymmetricLocal.eq_utTransvection_of_mem_center
    (by norm_num : 2 ≤ 3) hz
  generalize ((z : SpecialLinearGroup (Fin 3) F') : Matrix (Fin 3) (Fin 3) F') ⟨0, by omega⟩
    ⟨3 - 1, by omega⟩ = c at hzc
  rw [hzc]
  apply Subtype.ext
  apply Subtype.ext
  change transvection _ _ c * transvection _ _ c = 1
  rw [transvection_mul_transvection_same _ _
    (CFSG.ComponentClassification.SymmetricLocal.corner_lt (by norm_num : 2 ≤ 3)).ne,
    CharTwo.add_self_eq_zero, transvection_zero]

theorem model3_linear_b_ut :
    Model3B (SpecialLinearGroup (Fin 3) F') (unitriangular 3 F') := by
  intro x hx
  obtain ⟨B, hB⟩ := model3_linear_involution_conj x hx
  refine ⟨B, ?_⟩
  rcases hB with hB | hB
  · have h1 : B⁻¹ * x * B = 1 := Subtype.ext hB
    rw [h1]
    exact one_mem _
  · have hc := CFSG.ComponentClassification.SymmetricLocal.utTransvection_corner_mem_center
      (K := F') (n := 3) (by norm_num) 1
    exact ⟨_, hc, Subtype.ext hB.symm⟩

theorem model3_linear_c_ut :
    Model3C (SpecialLinearGroup (Fin 3) F') (unitriangular 3 F') := by
  intro τ hτ
  have h : ¬ (linE13 F' * linConj τ = 0 ∨ linConj τ * linE13 F' = 0) := fun h =>
    hτ (model3_linear_dichotomy τ h)
  push_neg at h
  exact model3_linear_generation _ le_sup_left fun A c hA =>
    model3_linear_transvection_mem τ h.1 h.2 A c hA

theorem model3_linear_a :
    Model3TildeA (SpecialLinearGroup (Fin 3) F') (Nat.card F') := by
  obtain ⟨R₀, hR₀⟩ := exists_sylow_unitriangular (K := F') 2 (n := 3) (by norm_num)
  exact model3TildeA_of_sylow R₀ (hR₀ ▸ model3_linear_a_ut)

theorem model3_linear_b : Model3TildeB (SpecialLinearGroup (Fin 3) F') := by
  obtain ⟨R₀, hR₀⟩ := exists_sylow_unitriangular (K := F') 2 (n := 3) (by norm_num)
  exact model3TildeB_of_sylow R₀ (hR₀ ▸ model3_linear_b_ut)

theorem model3_linear_c : Model3TildeC (SpecialLinearGroup (Fin 3) F') := by
  obtain ⟨R₀, hR₀⟩ := exists_sylow_unitriangular (K := F') 2 (n := 3) (by norm_num)
  exact model3TildeC_of_sylow R₀ (hR₀ ▸ model3_linear_c_ut)

theorem model3_linear :
    Model3Tilde (SpecialLinearGroup (Fin 3) F') (Nat.card F') :=
  ⟨model3_linear_a, model3_linear_b, model3_linear_c⟩

end Linear

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard
