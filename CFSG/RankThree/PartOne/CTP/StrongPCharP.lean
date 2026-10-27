module

public import CFSG.RankThree.PartOne.CTP.StrongPNoncentral

public section

namespace CFSG.RankThree.PartOne.StrongP

open Matrix CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

section Sp4

variable {K : Type} [Field K]

abbrev Ix4 := Fin 2 ⊕ Fin 2

def rk4 : Ix4 → ℕ := Sum.elim (fun i => i.val) (fun i => 3 - i.val)

theorem rk4_lt (i : Ix4) : rk4 i < 4 := by
  rcases i with i | i <;> simp [rk4] <;> omega

def sp4S : Matrix (Fin 2) (Fin 2) K := Matrix.single 1 1 1

def sp4A : Matrix (Fin 2) (Fin 2) K := 1 + Matrix.single 0 1 1

def sp4D : Matrix (Fin 2) (Fin 2) K := 1 - Matrix.single 1 0 1

def sp4X : Matrix Ix4 Ix4 K := Matrix.fromBlocks 1 sp4S 0 1

def sp4Xi : Matrix Ix4 Ix4 K := Matrix.fromBlocks 1 (-sp4S) 0 1

def sp4Y : Matrix Ix4 Ix4 K := Matrix.fromBlocks sp4A 0 0 sp4D

def sp4Yi : Matrix Ix4 Ix4 K :=
  Matrix.fromBlocks (1 - Matrix.single 0 1 1) 0 0 (1 + Matrix.single 1 0 1)

theorem sp4X_mul_Xi : (sp4X : Matrix Ix4 Ix4 K) * sp4Xi = 1 := by
  simp [sp4X, sp4Xi, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]

theorem sp4Xi_mul_X : (sp4Xi : Matrix Ix4 Ix4 K) * sp4X = 1 := by
  simp [sp4X, sp4Xi, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]

theorem sp4Y_mul_Yi : (sp4Y : Matrix Ix4 Ix4 K) * sp4Yi = 1 := by
  simp only [sp4Y, sp4Yi, Matrix.fromBlocks_multiply, sp4A, sp4D]
  rw [← Matrix.fromBlocks_one]
  congr 1
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply]
  · simp
  · simp
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply]

theorem sp4Yi_mul_Y : (sp4Yi : Matrix Ix4 Ix4 K) * sp4Y = 1 := by
  simp only [sp4Y, sp4Yi, Matrix.fromBlocks_multiply, sp4A, sp4D]
  rw [← Matrix.fromBlocks_one]
  congr 1
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply]
  · simp
  · simp
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply]

def sp4XU : GL Ix4 K := ⟨sp4X, sp4Xi, sp4X_mul_Xi, sp4Xi_mul_X⟩

def sp4YU : GL Ix4 K := ⟨sp4Y, sp4Yi, sp4Y_mul_Yi, sp4Yi_mul_Y⟩

theorem sp4X_symp : (sp4X : Matrix Ix4 Ix4 K)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 * sp4X =
    Matrix.fromBlocks 0 1 (-1) 0 := by
  have hS : (sp4S : Matrix (Fin 2) (Fin 2) K)ᵀ = sp4S := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [sp4S]
  simp [sp4X, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, hS]

theorem sp4Y_symp : (sp4Y : Matrix Ix4 Ix4 K)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 * sp4Y =
    Matrix.fromBlocks 0 1 (-1) 0 := by
  simp only [sp4Y, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, sp4A, sp4D]
  congr 1
  · simp
  · simp
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply]
  · simp
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply]
  · simp

theorem sp4X_unitri : IsUnitri rk4 (sp4XU : GL Ix4 K) := by
  intro i j h
  change ((sp4X : Matrix Ix4 Ix4 K) - 1) i j ≠ 0 at h
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [sp4X, sp4S, rk4, Matrix.fromBlocks] at h ⊢

theorem sp4Y_unitri : IsUnitri rk4 (sp4YU : GL Ix4 K) := by
  intro i j h
  change ((sp4Y : Matrix Ix4 Ix4 K) - 1) i j ≠ 0 at h
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [sp4Y, sp4A, sp4D, rk4, Matrix.fromBlocks] at h ⊢

theorem sp4_ne : (sp4XU : GL Ix4 K) * sp4YU ≠ sp4YU * sp4XU := by
  intro h
  have h' := congrArg (fun g : GL Ix4 K => (g : Matrix Ix4 Ix4 K)) h
  have := congrFun (congrFun h' (Sum.inl 0)) (Sum.inr 1)
  simp [sp4XU, sp4YU, sp4X, sp4Y, sp4S, sp4A, sp4D, Matrix.mul_apply, Matrix.single_apply,
    Matrix.one_apply] at this

theorem noncentralPair_sp4 {p : ℕ} [Fact p.Prime] [CharP K p] (hp : 4 ≤ p) :
    NoncentralPair p (StatedSp 2 K) := by
  refine noncentralPair_of_unitri (r := rk4) (m := 4) rk4_lt hp ?_ ?_ sp4X_unitri sp4Y_unitri
    sp4_ne
  · exact Subgroup.subset_closure sp4X_symp
  · exact Subgroup.subset_closure sp4Y_symp

end Sp4

end CFSG.RankThree.PartOne.StrongP
