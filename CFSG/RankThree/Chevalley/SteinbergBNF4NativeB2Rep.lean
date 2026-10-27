module

public import CFSG.RankThree.Chevalley.SteinbergBNF4NativeA2Rep
public import CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical

public noncomputable section

namespace CFSG.RankThree.Chevalley.SteinbergBN

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix
open CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical

variable {τ : Tag} {K : Type} [Field K]

theorem blockMat_torusElt
    {n : ℕ} {β : Fin n → Fin τ.rank → ℤ} (hβ : ∀ k, IsRoot τ (β k))
    (hinj : Function.Injective β) (i : Fin τ.rank) (t : Kˣ) :
    blockMat β (torusElt τ K i t) =
      diagonal fun k => ((t ^ (∑ j, τ.cartan i j * β k j) : Kˣ) : K) := by
  ext a b
  rw [blockMat_apply, torusElt_rootVec i t (hβ b), map_smul, rootCoord_rootVec_block hβ hinj,
    Matrix.diagonal_apply]
  by_cases h : a = b
  · subst h
    rw [ite_eq_left rfl, ite_eq_left rfl, smul_eq_mul, mul_one]
  · rw [ite_eq_right h, ite_eq_right h, smul_zero]

variable (K) in
@[expose] def f4J0 : Matrix (Fin 4) (Fin 4) K :=
  !![0, 0, 0, 1; 0, 0, -1, 0; 0, 1, 0, 0; -1, 0, 0, 0]

theorem f4B2BlockMat_x1 (c : K) :
    blockMat f4B2Weight (xUnit Tag.F4 K 1 c) = 1 + single 1 2 c := by
  rw [isSliceBlock_f4B2Weight.blockMat_xUnit_of_idx f4B2Idx f4B2Idx_spec one_mem_f4B2J,
    sum_range_four_smul _ _ f4B2_coeff_x1]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

theorem f4B2BlockMat_y1 (c : K) :
    blockMat f4B2Weight (yUnit Tag.F4 K 1 c) = 1 + single 2 1 c := by
  rw [isSliceBlock_f4B2Weight.blockMat_yUnit_of_idx f4B2Idx f4B2Idx_spec one_mem_f4B2J,
    sum_range_four_smul _ _ f4B2_coeff_y1]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

theorem f4B2BlockMat_x2 (c : K) :
    blockMat f4B2Weight (xUnit Tag.F4 K 2 c) = 1 + single 0 1 c + single 2 3 c := by
  rw [isSliceBlock_f4B2Weight.blockMat_xUnit_of_idx f4B2Idx f4B2Idx_spec two_mem_f4B2J,
    sum_range_four_smul _ _ f4B2_coeff_x2]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

theorem f4B2BlockMat_y2 (c : K) :
    blockMat f4B2Weight (yUnit Tag.F4 K 2 c) = 1 + single 1 0 c + single 3 2 c := by
  rw [isSliceBlock_f4B2Weight.blockMat_yUnit_of_idx f4B2Idx f4B2Idx_spec two_mem_f4B2J,
    sum_range_four_smul _ _ f4B2_coeff_y2]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

theorem isometry_one_add_single_12 (c : K) :
    (1 + single 1 2 c : Matrix (Fin 4) (Fin 4) K)ᵀ * f4J0 K * (1 + single 1 2 c) = f4J0 K := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [f4J0, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply]

theorem isometry_one_add_single_21 (c : K) :
    (1 + single 2 1 c : Matrix (Fin 4) (Fin 4) K)ᵀ * f4J0 K * (1 + single 2 1 c) = f4J0 K := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [f4J0, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply]

theorem isometry_x2 (c : K) :
    (1 + single 0 1 c + single 2 3 c : Matrix (Fin 4) (Fin 4) K)ᵀ * f4J0 K *
      (1 + single 0 1 c + single 2 3 c) = f4J0 K := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [f4J0, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply]

theorem isometry_y2 (c : K) :
    (1 + single 1 0 c + single 3 2 c : Matrix (Fin 4) (Fin 4) K)ᵀ * f4J0 K *
      (1 + single 1 0 c + single 3 2 c) = f4J0 K := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [f4J0, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply]

variable (K) in
abbrev f4B2BlockHom
    : subsystemGroup Tag.F4 K {1, 2} →* GL (Fin 4) K :=
  isSliceBlock_f4B2Weight.blockHom

theorem f4B2BlockHom_mem
    (g : subsystemGroup Tag.F4 K {1, 2}) :
    f4B2BlockHom K g ∈ matrixIsometryGroup (f4J0 K) := by
  refine map_mem_of_gen _ _ (fun k hk c => ?_) (fun k hk c => ?_) g
  · rcases (show k = 1 ∨ k = 2 from hk) with rfl | rfl
    · rw [mem_matrixIsometryGroup, IsSliceBlock.coe_blockHom, coe_qx, f4B2BlockMat_x1]
      exact isometry_one_add_single_12 c
    · rw [mem_matrixIsometryGroup, IsSliceBlock.coe_blockHom, coe_qx, f4B2BlockMat_x2]
      exact isometry_x2 c
  · rcases (show k = 1 ∨ k = 2 from hk) with rfl | rfl
    · rw [mem_matrixIsometryGroup, IsSliceBlock.coe_blockHom, coe_qy, f4B2BlockMat_y1]
      exact isometry_one_add_single_21 c
    · rw [mem_matrixIsometryGroup, IsSliceBlock.coe_blockHom, coe_qy, f4B2BlockMat_y2]
      exact isometry_y2 c

variable (K) in
@[expose] def f4B2Rep
    : subsystemGroup Tag.F4 K {1, 2} →* matrixIsometryGroup (f4J0 K) :=
  (f4B2BlockHom K).codRestrict _ f4B2BlockHom_mem

theorem coe_f4B2Rep
    (g : subsystemGroup Tag.F4 K {1, 2}) :
    (((f4B2Rep K g : matrixIsometryGroup (f4J0 K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      blockMat f4B2Weight (g : ModGL Tag.F4 K) :=
  rfl

theorem f4B2_weights_pairing : ∀ k : Fin 4,
    (∑ j, Tag.F4.cartan 1 j * f4B2Weight k j) = (![0, 1, -1, 0] : Fin 4 → ℤ) k ∧
    (∑ j, Tag.F4.cartan 2 j * f4B2Weight k j) = (![1, -1, 1, -1] : Fin 4 → ℤ) k := by
  decide +kernel

theorem f4B2Rep_torus (t u : Kˣ) :
    (((f4B2Rep K ⟨torusElt Tag.F4 K 1 t * torusElt Tag.F4 K 2 u, torusElt_pair_mem 1 2 t u⟩ :
      matrixIsometryGroup (f4J0 K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      diagonal ![(u : K), (t : K) * (u : K)⁻¹, (t : K)⁻¹ * u, (u : K)⁻¹] := by
  rw [coe_f4B2Rep, isSliceBlock_f4B2Weight.blockMat_mul'
      (subsystemTorus_le_subsystemGroup (torusElt_mem_subsystemTorus (right_mem_pair 1 2) u)),
    blockMat_torusElt isSliceBlock_f4B2Weight.isRoot isSliceBlock_f4B2Weight.injective,
    blockMat_torusElt isSliceBlock_f4B2Weight.isRoot isSliceBlock_f4B2Weight.injective,
    diagonal_mul_diagonal]
  congr 1
  funext k
  rw [(f4B2_weights_pairing k).1, (f4B2_weights_pairing k).2]
  fin_cases k <;> simp [mul_comm]

end CFSG.RankThree.Chevalley.SteinbergBN
