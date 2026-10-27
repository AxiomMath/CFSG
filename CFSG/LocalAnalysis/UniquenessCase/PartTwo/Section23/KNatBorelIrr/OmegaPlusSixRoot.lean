module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusLevi

import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitCoverTorus
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitGeometryPositive

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NatBorelIrr

open CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open scoped MatrixGroups

@[expose] noncomputable def plusRootAlpha (K : Type) [Field K] :
    SL(2, K) →* ((Fin 3 ⊕ Fin 3 → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K)) :=
  (plusFlagLevi K (r := 3) (a := 0) (b := 2) (by norm_num)).comp
    (Matrix.SpecialLinearGroup.toGL : SL(2, K) →* GL (Fin 2) K)

variable {K : Type} [Field K]

private theorem not_mem_range_plusFinIdx_two_L12 :
    (2 : Fin 3) ∉ Set.range (plusFinIdx (r := 3) (a := 0) (b := 2) (by norm_num)) := by
  rintro ⟨k, hk⟩
  have hk' : (k : ℕ) = 2 := by simpa [plusFinIdx] using congrArg Fin.val hk
  have hklt : (k : ℕ) < 2 := by simpa using k.isLt
  omega

private theorem extendMat_alpha_L12 (c : Kˣ) :
    extendMat (plusFinIdx_injective (r := 3) (a := 0) (b := 2) (by norm_num))
        (Matrix.diagonal (fun i : Fin 2 => (![c, c⁻¹] i : K))) =
      Matrix.diagonal (fun i : Fin 3 => (![c, c⁻¹, 1] i : K)) := by
  unfold extendMat
  rw [← Matrix.diagonal_one]
  rw [Matrix.fromBlocks_diagonal, Matrix.submatrix_diagonal_equiv]
  rw [Matrix.diagonal_eq_diagonal_iff]
  intro x
  fin_cases x
  · change Sum.elim (fun i : Fin 2 => (![c, c⁻¹] i : K)) (fun _ => (1 : K))
        (extendEquiv (plusFinIdx_injective (r := 3) (a := 0) (b := 2) (by norm_num))
          (plusFinIdx (r := 3) (a := 0) (b := 2) (by norm_num) ⟨0, by norm_num⟩)) =
        ((![c, c⁻¹, 1] (0 : Fin 3) : Kˣ) : K)
    rw [extendEquiv_apply_map]
    simp
  · change Sum.elim (fun i : Fin 2 => (![c, c⁻¹] i : K)) (fun _ => (1 : K))
        (extendEquiv (plusFinIdx_injective (r := 3) (a := 0) (b := 2) (by norm_num))
          (plusFinIdx (r := 3) (a := 0) (b := 2) (by norm_num) ⟨1, by norm_num⟩)) =
        ((![c, c⁻¹, 1] (1 : Fin 3) : Kˣ) : K)
    rw [extendEquiv_apply_map]
    simp
  · change Sum.elim (fun i : Fin 2 => (![c, c⁻¹] i : K)) (fun _ => (1 : K))
        (extendEquiv (plusFinIdx_injective (r := 3) (a := 0) (b := 2) (by norm_num))
          (2 : Fin 3)) =
        ((![c, c⁻¹, 1] (2 : Fin 3) : Kˣ) : K)
    rw [extendEquiv_apply_of_not_mem (plusFinIdx_injective (r := 3) (a := 0) (b := 2)
      (by norm_num)) not_mem_range_plusFinIdx_two_L12]
    simp

theorem plusRootAlpha_mem [Finite K] [CharP K 2] (A : SL(2, K)) :
    plusRootAlpha K A ∈ plusFlagStab K 3 ({2, 3} : Finset ℕ) := by
  show plusFlagLevi K (r := 3) (a := 0) (b := 2) (by norm_num)
      (Matrix.SpecialLinearGroup.toGL A) ∈ plusFlagStab K 3 ({2, 3} : Finset ℕ)
  refine mem_plusFlagStab.2 ⟨maxStab_le_orthElementaryGroup (le_refl 3)
    (levi_mem_maxStab _), fun d hd => ?_⟩
  have hd2 : 2 ≤ d := by simp at hd; omega
  have hd3 : d ≤ 3 := by simp at hd; omega
  refine smul_flag_of_plusCut hd3 ?_ ?_
  · exact plusCut_plusFlagLevi (r := 3) (a := 0) (b := 2) (by norm_num)
      (Matrix.SpecialLinearGroup.toGL A) hd3 (Or.inr hd2)
  · rw [← map_inv]
    exact plusCut_plusFlagLevi (r := 3) (a := 0) (b := 2) (by norm_num)
      ((Matrix.SpecialLinearGroup.toGL A)⁻¹) hd3 (Or.inr hd2)

theorem plusExtGL_alpha_eq_diagGL (c : Kˣ) (A : SL(2, K))
    (hA : (A : Matrix (Fin 2) (Fin 2) K) = !![(c : K), 0; 0, ((c⁻¹ : Kˣ) : K)]) :
    plusExtGL (plusFinIdx_injective (r := 3) (a := 0) (b := 2) (by norm_num))
        (Matrix.SpecialLinearGroup.toGL A : GL (Fin 2) K) = diagGL ![c, c⁻¹, 1] := by
  have hB : (!![(c : K), 0; 0, ((c⁻¹ : Kˣ) : K)] : Matrix (Fin 2) (Fin 2) K) =
      Matrix.diagonal (fun i : Fin 2 => (![c, c⁻¹] i : K)) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply]
  apply Units.ext
  rw [coe_plusExtGL, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hA, hB]
  rw [extendMat_alpha_L12 c]
  rfl

theorem plusRootAlpha_eq_torusElt (c : Kˣ) (A : SL(2, K))
    (hA : (A : Matrix (Fin 2) (Fin 2) K) = !![(c : K), 0; 0, ((c⁻¹ : Kˣ) : K)]) :
    plusRootAlpha K A = torusElt 3 K ![c, c⁻¹, 1] := by
  rw [torusElt_eq_levi]
  exact congrArg (levi 3 K) (plusExtGL_alpha_eq_diagGL c A hA)

theorem torusElt_alpha_mem_borel [Finite K] [CharP K 2] (c : Kˣ) :
    torusElt 3 K ![c, c⁻¹, 1] ∈ borel 3 K := by
  refine torus_le_borel ?_
  exact mem_torus.2 ⟨torusElt_mem_orthElementaryGroup (le_refl 3) ![c, c⁻¹, 1],
    ![c, c⁻¹, 1], rfl⟩

theorem torusElt_alpha_apply_e0 (c : Kˣ) :
    torusElt 3 K ![c, c⁻¹, 1] (Pi.single (Sum.inl 0) 1 : Fin 3 ⊕ Fin 3 → K) =
      (c : K) • (Pi.single (Sum.inl 0) 1 : Fin 3 ⊕ Fin 3 → K) := by
  funext x
  rw [torusElt_apply]
  rcases x with i | i
  · fin_cases i <;> simp [Pi.single_apply]
  · fin_cases i <;> simp [Pi.single_apply]

end CFSG.LocalAnalysis.UniquenessCase.UC22.NatBorelIrr
