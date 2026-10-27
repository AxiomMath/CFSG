module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80U3Mod

public section

namespace CFSG.Quasithin.E2P.Asc80

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.Assembly.LowTwoRank CFSG.Quasithin.A312U3

variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F]

@[expose] noncomputable def mkSU3 (hF : Nat.card F = p ^ 2) (M : Matrix (Fin 3) (Fin 3) F)
    (hdet : M.det = 1) (hu : (M.map (uniData hF).bar)ᵀ * M = 1) : SU3F p F :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M (by rw [hdet]; exact one_ne_zero),
    (mem_unitarySU_iff (uniData hF)).mpr ⟨hdet, hu⟩⟩

theorem unitary_cols (hF : Nat.card F = p ^ 2) (g : SU3F p F) (j k : Fin 3) :
    ∑ i, (uniData hF).bar (matU g i j) * matU g i k = if j = k then 1 else 0 := by
  have h := ((mem_unitarySU_iff (uniData hF)).mp g.2).2
  have := congrFun (congrFun h j) k
  simpa [Matrix.mul_apply, Matrix.one_apply, matU] using this

theorem unitary_rows (hF : Nat.card F = p ^ 2) (g : SU3F p F) (i k : Fin 3) :
    ∑ j, matU g i j * (uniData hF).bar (matU g k j) = if i = k then 1 else 0 := by
  have h := ((mem_unitarySU_iff (uniData hF)).mp g.2).2
  have h' := mul_eq_one_comm.mp h
  have := congrFun (congrFun h' i) k
  simpa [Matrix.mul_apply, Matrix.one_apply, matU] using this

@[expose] def dsMat (F : Type) [Field F] (i : Fin 3) : Matrix (Fin 3) (Fin 3) F :=
  Matrix.diagonal fun j => if j = i then 1 else -1

theorem det_dsMat (i : Fin 3) : (dsMat F i).det = 1 := by
  fin_cases i <;> simp [dsMat, Matrix.det_diagonal, Fin.prod_univ_three]

theorem dsMat_unitary (hF : Nat.card F = p ^ 2) (i : Fin 3) :
    ((dsMat F i).map (uniData (p := p) hF).bar)ᵀ * dsMat F i = 1 := by
  rw [dsMat, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext j
  by_cases h : j = i <;> simp [h]

@[expose] noncomputable def dsU (hF : Nat.card F = p ^ 2) (i : Fin 3) : SU3F p F :=
  mkSU3 hF (dsMat F i) (det_dsMat i) (dsMat_unitary hF i)

theorem matU_dsU (hF : Nat.card F = p ^ 2) (i : Fin 3) : matU (dsU hF i) = dsMat F i := rfl

@[expose] def swapMat (F : Type) [Field F] : Matrix (Fin 3) (Fin 3) F :=
  !![0, 1, 0; 1, 0, 0; 0, 0, -1]

theorem det_swapMat : (swapMat F).det = 1 := by
  simp [swapMat, Matrix.det_fin_three]

theorem swapMat_unitary (hF : Nat.card F = p ^ 2) :
    ((swapMat F).map (uniData (p := p) hF).bar)ᵀ * swapMat F = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapMat, Matrix.mul_apply, Fin.sum_univ_three]

@[expose] noncomputable def swapU (hF : Nat.card F = p ^ 2) : SU3F p F :=
  mkSU3 hF (swapMat F) det_swapMat (swapMat_unitary hF)

theorem matU_swapU (hF : Nat.card F = p ^ 2) : matU (swapU hF) = swapMat F := rfl

@[expose] def flipMat (F : Type) [Field F] : Matrix (Fin 3) (Fin 3) F :=
  !![0, 0, 1; 0, -1, 0; 1, 0, 0]

theorem det_flipMat : (flipMat F).det = 1 := by
  simp [flipMat, Matrix.det_fin_three]

theorem flipMat_unitary (hF : Nat.card F = p ^ 2) :
    ((flipMat F).map (uniData (p := p) hF).bar)ᵀ * flipMat F = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [flipMat, Matrix.mul_apply, Fin.sum_univ_three]

@[expose] noncomputable def flipU (hF : Nat.card F = p ^ 2) : SU3F p F :=
  mkSU3 hF (flipMat F) det_flipMat (flipMat_unitary hF)

theorem matU_flipU (hF : Nat.card F = p ^ 2) : matU (flipU hF) = flipMat F := rfl

theorem dsU_mem_leviU (hp2 : p ≠ 2) (hF : Nat.card F = p ^ 2) (i : Fin 3) :
    dsU hF i ∈ leviU hF := by
  rw [mem_leviU_iff hp2 hF]
  fin_cases i <;> simp [matU_dsU, dsMat]

theorem swapU_mem_leviU (hp2 : p ≠ 2) (hF : Nat.card F = p ^ 2) : swapU hF ∈ leviU hF := by
  rw [mem_leviU_iff hp2 hF]
  simp [matU_swapU, swapMat]

theorem flipU_not_mem_leviU (hp2 : p ≠ 2) (hF : Nat.card F = p ^ 2) : flipU hF ∉ leviU hF := by
  rw [mem_leviU_iff hp2 hF]
  intro h
  have := h.1
  simp [matU_flipU, flipMat] at this

end CFSG.Quasithin.E2P.Asc80
