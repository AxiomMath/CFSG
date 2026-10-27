module

public import CFSG.Monster.Xi.Grey
public import CFSG.Monster.Spin.Defs
public import CFSG.Monster.Dyadic
import CFSG.Monster.Spin.Coords
import CFSG.Monster.FourierTriality

public noncomputable section

namespace CFSG.Monster.Xi

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin Matrix

@[expose] def XiGamma : Matrix SpinIdx SpinIdx ℚ :=
  (1 / 8 : ℚ) • ∑ μ : Fin 6 → ZMod 2, sgn (qG μ) • Dmat (gammaD μ)

@[expose] def XiG : Matrix SpinIdx SpinIdx ℚ :=
  (1 / 8 : ℚ) • ∑ μ : Fin 6 → ZMod 2, sgn (qG μ) • Tmat (greyC μ)

@[expose] def Ximat : Matrix SpinIdx SpinIdx ℚ := XiGamma * XiG

@[expose] def J4 : Matrix (Fin 4) (Fin 4) ℚ := Matrix.of fun _ _ => 1

@[expose] def C4 : Matrix (Fin 4) (Fin 4) ℚ :=
  (1 - (1 / 2 : ℚ) • J4) * Matrix.diagonal ![-1, 1, 1, 1]

@[expose] def gXi : Matrix (Fin 24) (Fin 24) ℚ :=
  Matrix.of fun i i' => if col i = col i' then C4 (row i) (row i') else 0

theorem gXi_apply (i i' : Fin 24) : gXi i i' = if col i = col i' then C4 (row i) (row i') else 0 :=
  rfl

theorem gXi_coord (r : Fin 4) (j : Fin 6) (r' : Fin 4) (j' : Fin 6) :
    gXi (coord r j) (coord r' j') = if j = j' then C4 r r' else 0 := by
  rw [gXi_apply, col_coord, col_coord, row_coord, row_coord]

theorem C4_eq : C4 = !![-1 / 2, -1 / 2, -1 / 2, -1 / 2; 1 / 2, 1 / 2, -1 / 2, -1 / 2;
    1 / 2, -1 / 2, 1 / 2, -1 / 2; 1 / 2, -1 / 2, -1 / 2, 1 / 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [C4, J4, Matrix.mul_diagonal, Matrix.sub_apply] <;> norm_num

theorem Dmat_mem_dyadic (δ : Cocode) (i j : SpinIdx) : Dmat δ i j ∈ dyadic := by
  rcases Dmat_apply_mem δ i j with h | h | h <;> rw [h]
  · exact dyadic.zero_mem
  · exact dyadic.one_mem
  · exact dyadic.neg_mem dyadic.one_mem

theorem Tmat_mem_dyadic (a : C) (i j : SpinIdx) : Tmat a i j ∈ dyadic := by
  rcases Tmat_apply_mem a i j with h | h | h <;> rw [h]
  · exact dyadic.zero_mem
  · exact dyadic.one_mem
  · exact dyadic.neg_mem dyadic.one_mem

theorem one_div_eight_mem_dyadic : (1 / 8 : ℚ) ∈ dyadic := ⟨3, by norm_num⟩

private theorem average_mem_dyadic (M : (Fin 6 → ZMod 2) → Matrix SpinIdx SpinIdx ℚ)
    (hM : ∀ μ i j, M μ i j ∈ dyadic) (i j : SpinIdx) :
    ((1 / 8 : ℚ) • ∑ μ : Fin 6 → ZMod 2, sgn (qG μ) • M μ) i j ∈ dyadic := by
  rw [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  refine dyadic.mul_mem one_div_eight_mem_dyadic (dyadic.sum_mem fun μ _ => ?_)
  rw [Matrix.smul_apply, smul_eq_mul]
  exact dyadic.mul_mem (sgn_mem_dyadic _) (hM μ i j)

theorem XiGamma_mem_dyadic (i j : SpinIdx) : XiGamma i j ∈ dyadic :=
  average_mem_dyadic _ (fun μ => Dmat_mem_dyadic (gammaD μ)) i j

theorem XiG_mem_dyadic (i j : SpinIdx) : XiG i j ∈ dyadic :=
  average_mem_dyadic _ (fun μ => Tmat_mem_dyadic (greyC μ)) i j

theorem Ximat_mem_dyadic (i j : SpinIdx) : Ximat i j ∈ dyadic :=
  mul_mem_dyadic XiGamma_mem_dyadic XiG_mem_dyadic i j

theorem C4_mem_dyadic (r r' : Fin 4) : C4 r r' ∈ dyadic := by
  have h2 : (1 / 2 : ℚ) ∈ dyadic := ⟨1, by norm_num⟩
  have h : C4 r r' = 1 / 2 ∨ C4 r r' = -(1 / 2) := by
    rw [C4_eq]
    fin_cases r <;> fin_cases r' <;> simp <;> norm_num
  rcases h with h | h <;> rw [h]
  · exact h2
  · exact dyadic.neg_mem h2

theorem gXi_mem_dyadic (i i' : Fin 24) : gXi i i' ∈ dyadic := by
  rw [gXi_apply]
  split_ifs
  · exact C4_mem_dyadic _ _
  · exact dyadic.zero_mem

theorem xi_explicit_matrix_data :
    Fintype.card (Fin 6 → ZMod 2) = 64 ∧
    XiGamma = (1 / 8 : ℚ) • ∑ μ : Fin 6 → ZMod 2, sgn (qG μ) • Dmat (gammaD μ) ∧
    XiG = (1 / 8 : ℚ) • ∑ μ : Fin 6 → ZMod 2, sgn (qG μ) • Tmat (greyC μ) ∧
    Ximat = XiGamma * XiG ∧
    (∀ i j : SpinIdx, XiGamma i j ∈ dyadic ∧ XiG i j ∈ dyadic ∧ Ximat i j ∈ dyadic) ∧
    J4 = Matrix.of (fun _ _ => 1) ∧
    C4 = (1 - (1 / 2 : ℚ) • J4) * Matrix.diagonal ![-1, 1, 1, 1] ∧
    C4 = !![-1 / 2, -1 / 2, -1 / 2, -1 / 2; 1 / 2, 1 / 2, -1 / 2, -1 / 2;
      1 / 2, -1 / 2, 1 / 2, -1 / 2; 1 / 2, -1 / 2, -1 / 2, 1 / 2] ∧
    (∀ (r : Fin 4) (j : Fin 6) (r' : Fin 4) (j' : Fin 6),
      gXi (coord r j) (coord r' j') = if j = j' then C4 r r' else 0) ∧
    (∀ i i' : Fin 24, gXi i i' ∈ dyadic) :=
  ⟨by simp, rfl, rfl, rfl,
    fun i j => ⟨XiGamma_mem_dyadic i j, XiG_mem_dyadic i j, Ximat_mem_dyadic i j⟩, rfl, rfl, C4_eq,
    gXi_coord, gXi_mem_dyadic⟩

end CFSG.Monster.Xi
