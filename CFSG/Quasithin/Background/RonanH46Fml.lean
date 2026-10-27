module

public import CFSG.Quasithin.Background.RonanH44Orth

public section

namespace CFSG.Quasithin.RonanH46

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H.SU3 Matrix
  CFSG.Quasithin.RonanH44
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

@[expose] def hermBlkZ (X : HMod n K) : Matrix (Fin 2) (Fin 2) K :=
  fun i j => mat X i.succ j.succ

@[expose] def blkMatZ (g : Matrix (Fin 3) (Fin 3) K) : Matrix (Fin 2) (Fin 2) K :=
  fun i j => g i.succ j.succ

private theorem mat_rho_entry (hK : Nat.card K = (2 ^ n) ^ 2) {g : SL(3, K)} (X : HMod n K)
    (i j : Fin 3) : mat (rho hK g X) i j = ∑ k, ∑ l, (g : Matrix (Fin 3) (Fin 3) K) i k *
      mat X k l * bar n ((g : Matrix (Fin 3) (Fin 3) K) j l) := by
  simp [mat_rho, tw, conjM, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply,
    Matrix.map_apply]
  ring

private theorem mat_col_zero_eq_bar (hK : Nat.card K = (2 ^ n) ^ 2) (X : HMod n K) (k : Fin 3) :
    mat X k 0 = bar n (mat X 0 k) := by
  rw [← herm_apply X 0 k, bar_bar hK]

theorem rhoW_entry22 (hK : Nat.card K = (2 ^ n) ^ 2) {g : SL(3, K)} (hg : g ∈ perfW K)
    (X : HMod n K) : mat (rho hK g X) 2 2 = mat X 2 2 := by
  obtain ⟨h20, h21, h22⟩ := hg
  rw [mat_rho_entry]
  simp [Fin.sum_univ_three, h20, h21, h22]

theorem rhoW_col (hK : Nat.card K = (2 ^ n) ^ 2) {g : SL(3, K)} (hg : g ∈ perfW K)
    (X : HMod n K) (i : Fin 2) :
    mat (rho hK g X) (Fin.castLE (by decide) i) 2 =
      (blkMat (g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![mat X 0 2, mat X 1 2]) i +
        (g : Matrix (Fin 3) (Fin 3) K) (Fin.castLE (by decide) i) 2 * mat X 2 2 := by
  obtain ⟨h20, h21, h22⟩ := hg
  rw [mat_rho_entry]
  fin_cases i <;>
    simp [blkMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two, h20, h21,
      h22] <;>
    ring

theorem rhoZ_block (hK : Nat.card K = (2 ^ n) ^ 2) {g : SL(3, K)} (hg : g ∈ perfZ K)
    (X : HMod n K) :
    hermBlkZ (rho hK g X) = blkMatZ (g : Matrix (Fin 3) (Fin 3) K) * hermBlkZ X *
      ((blkMatZ (g : Matrix (Fin 3) (Fin 3) K)).map (bar n))ᵀ := by
  obtain ⟨h10, h20, -⟩ := hg
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermBlkZ, blkMatZ, mat_rho_entry, Matrix.mul_apply, Fin.sum_univ_three,
      Fin.sum_univ_two, Matrix.transpose_apply, Matrix.map_apply, h10, h20] <;>
    ring

theorem rhoZ_row (hK : Nat.card K = (2 ^ n) ^ 2) {g : SL(3, K)} (hg : g ∈ perfZ K)
    (X : HMod n K) (j : Fin 2) :
    mat (rho hK g X) 0 j.succ =
      Matrix.vecMul (![mat X 0 1, mat X 0 2] + Matrix.vecMul ![(g : Matrix (Fin 3) (Fin 3) K) 0 1,
          (g : Matrix (Fin 3) (Fin 3) K) 0 2] (hermBlkZ X))
        ((blkMatZ (g : Matrix (Fin 3) (Fin 3) K)).map (bar n))ᵀ j := by
  obtain ⟨h10, h20, h00⟩ := hg
  rw [mat_rho_entry]
  fin_cases j <;>
    simp [Matrix.vecMul, dotProduct, hermBlkZ, blkMatZ, Fin.sum_univ_three, Fin.sum_univ_two,
      Matrix.transpose_apply, Matrix.map_apply, h10, h20, h00] <;>
    ring

theorem rhoZ_corner (hK : Nat.card K = (2 ^ n) ^ 2) {g : SL(3, K)} (hg : g ∈ perfZ K)
    (X : HMod n K) :
    mat (rho hK g X) 0 0 = mat X 0 0 +
      ∑ i : Fin 2, (g : Matrix (Fin 3) (Fin 3) K) 0 i.succ * bar n (mat X 0 i.succ) +
      ∑ i : Fin 2, mat X 0 i.succ * bar n ((g : Matrix (Fin 3) (Fin 3) K) 0 i.succ) +
      ∑ i : Fin 2, ∑ j : Fin 2, (g : Matrix (Fin 3) (Fin 3) K) 0 i.succ * hermBlkZ X i j *
        bar n ((g : Matrix (Fin 3) (Fin 3) K) 0 j.succ) := by
  obtain ⟨h10, h20, h00⟩ := hg
  rw [mat_rho_entry]
  simp [hermBlkZ, Fin.sum_univ_three, Fin.sum_univ_two, mat_col_zero_eq_bar hK X 1,
    mat_col_zero_eq_bar hK X 2, h10, h20, h00]
  ring

end CFSG.Quasithin.RonanH46
