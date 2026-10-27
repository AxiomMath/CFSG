module

public import CFSG.ClassicalInvolution.WeakCT.Defs
import CFSG.ClassicalInvolution.WeakCT.Amalgam
public import CFSG.ClassicalInvolution.Phan.Blocks
public import CFSG.LieType.CurtisTits.SpecialLinear

public section

namespace CFSG.StandardType.FF81.Blocks

open Matrix CFSG.ClassicalInvolution.WeakCT
open CFSG.ClassicalInvolution.Phan (blockMat blockMat_apply)
open scoped MatrixGroups

variable {N : ℕ}

theorem entries_of_commute_single {g : Matrix (Fin N) (Fin N) (ZMod 2)} {i j : Fin N}
    (h : g * single i j (1 : ZMod 2) = single i j 1 * g) :
    (∀ k, k ≠ i → g k i = 0) ∧ (∀ l, l ≠ j → g j l = 0) ∧ g i i = g j j := by
  refine ⟨fun k hk => ?_, fun l hl => ?_, ?_⟩
  · have e := congrFun (congrFun h k) j
    rwa [mul_single_apply_same, mul_one, single_mul_apply_of_ne _ _ _ _ _ hk] at e
  · have e := congrFun (congrFun h i) l
    rwa [mul_single_apply_of_ne _ _ _ _ _ hl, single_mul_apply_same, one_mul, eq_comm] at e
  · have e := congrFun (congrFun h i) j
    rwa [mul_single_apply_same, mul_one, single_mul_apply_same, one_mul] at e

theorem commute_single_of_entries {g : Matrix (Fin N) (Fin N) (ZMod 2)} {i j : Fin N}
    (hcol : ∀ k, k ≠ i → g k i = 0) (hrow : ∀ l, l ≠ j → g j l = 0) (hd : g i i = g j j) :
    g * single i j (1 : ZMod 2) = single i j 1 * g := by
  ext k l
  rcases eq_or_ne l j with rfl | hl
  · rw [mul_single_apply_same, mul_one]
    rcases eq_or_ne k i with rfl | hk
    · rw [single_mul_apply_same, one_mul, hd]
    · rw [hcol k hk, single_mul_apply_of_ne _ _ _ _ _ hk]
  · rw [mul_single_apply_of_ne _ _ _ _ _ hl]
    rcases eq_or_ne k i with rfl | hk
    · rw [single_mul_apply_same, one_mul, hrow l hl]
    · rw [single_mul_apply_of_ne _ _ _ _ _ hk]

theorem commute_one_add_single_iff {g : Matrix (Fin N) (Fin N) (ZMod 2)} {i j : Fin N} :
    g * (1 + single i j (1 : ZMod 2)) = (1 + single i j 1) * g ↔
      g * single i j (1 : ZMod 2) = single i j 1 * g := by
  rw [mul_add, add_mul, mul_one, one_mul]
  exact add_right_inj g

abbrev tvU : SL(2, ZMod 2) :=
  Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) (1 : ZMod 2)

abbrev tvD : SL(2, ZMod 2) :=
  Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) (1 : ZMod 2)

theorem sl2_cases (A : SL(2, ZMod 2)) :
    A = 1 ∨ A = tvU ∨ A = tvD ∨ A = tvU * tvD ∨ A = tvD * tvU ∨ A = tvU * tvD * tvU := by
  revert A
  decide

theorem single_comm_of_commute {g : SL(N, ZMod 2)} {i j : Fin N} (hij : i ≠ j)
    (h : Commute g (Matrix.SpecialLinearGroup.transvection hij (1 : ZMod 2))) :
    (g : Matrix (Fin N) (Fin N) (ZMod 2)) * single i j 1 =
      single i j 1 * (g : Matrix (Fin N) (Fin N) (ZMod 2)) := by
  have h' := congrArg (fun x : SL(N, ZMod 2) => (x : Matrix (Fin N) (Fin N) (ZMod 2))) h.eq
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe] at h'
  exact commute_one_add_single_iff.1 h'

theorem commute_of_single_comm {g : SL(N, ZMod 2)} {i j : Fin N} (hij : i ≠ j)
    (h : (g : Matrix (Fin N) (Fin N) (ZMod 2)) * single i j 1 =
      single i j 1 * (g : Matrix (Fin N) (Fin N) (ZMod 2))) :
    Commute g (Matrix.SpecialLinearGroup.transvection hij (1 : ZMod 2)) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe]
  exact commute_one_add_single_iff.2 h

theorem diag_eq_one_of_row {g : SL(N, ZMod 2)} {j : Fin N}
    (hrow : ∀ l, l ≠ j → (g : Matrix (Fin N) (Fin N) (ZMod 2)) j l = 0) :
    (g : Matrix (Fin N) (Fin N) (ZMod 2)) j j = 1 := by
  have h01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases h01 ((g : Matrix (Fin N) (Fin N) (ZMod 2)) j j) with h | h
  · have hdet := Matrix.det_eq_zero_of_row_eq_zero (A := (g : Matrix (Fin N) (Fin N) (ZMod 2))) j
      (fun l => by rcases eq_or_ne l j with rfl | hl; exacts [h, hrow l hl])
    rw [g.2] at hdet
    exact absurd hdet one_ne_zero
  · exact h

theorem commute_blockSL2_succ {n : ℕ} (g : SL(n + 1, ZMod 2)) (i : ℕ) (hi : i + 2 < n)
    (h0 : ∀ A, Commute g (blockSL2 (ZMod 2) n ⟨i, by omega⟩ A))
    (h2 : ∀ A, Commute g (blockSL2 (ZMod 2) n ⟨i + 2, hi⟩ A)) (A : SL(2, ZMod 2)) :
    Commute g (blockSL2 (ZMod 2) n ⟨i + 1, by omega⟩ A) := by
  set G := (g : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2)) with hG
  set i0 : Fin n := ⟨i, by omega⟩
  set i1 : Fin n := ⟨i + 1, by omega⟩
  set i2 : Fin n := ⟨i + 2, hi⟩
  have hb : i0.succ = i1.castSucc := Fin.ext rfl
  have hc : i1.succ = i2.castSucc := Fin.ext rfl
  have hU0 := single_comm_of_commute _
    ((blockSL2_transvection_up (K := ZMod 2) i0 1) ▸ h0 tvU)
  have hD0 := single_comm_of_commute _
    ((blockSL2_transvection_down (K := ZMod 2) i0 1) ▸ h0 tvD)
  have hU2 := single_comm_of_commute _
    ((blockSL2_transvection_up (K := ZMod 2) i2 1) ▸ h2 tvU)
  have hD2 := single_comm_of_commute _
    ((blockSL2_transvection_down (K := ZMod 2) i2 1) ▸ h2 tvD)
  obtain ⟨-, hrowb, -⟩ := entries_of_commute_single hU0
  obtain ⟨hcolb, -, -⟩ := entries_of_commute_single hD0
  obtain ⟨hcolc, -, -⟩ := entries_of_commute_single hU2
  obtain ⟨-, hrowc, -⟩ := entries_of_commute_single hD2
  rw [hb] at hrowb hcolb
  have hbb := diag_eq_one_of_row hrowb
  have hcc := diag_eq_one_of_row hrowc
  rw [← hc] at hcolc hrowc hcc
  have hTU : Commute g (blockSL2 (ZMod 2) n i1 tvU) := by
    rw [blockSL2_transvection_up]
    exact commute_of_single_comm _
      (commute_single_of_entries hcolb hrowc (hbb.trans hcc.symm))
  have hTD : Commute g (blockSL2 (ZMod 2) n i1 tvD) := by
    rw [blockSL2_transvection_down]
    exact commute_of_single_comm _
      (commute_single_of_entries hcolc hrowb (hcc.trans hbb.symm))
  rcases sl2_cases A with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [map_one]
    exact Commute.one_right g
  · exact hTU
  · exact hTD
  · rw [map_mul]
    exact hTU.mul_right hTD
  · rw [map_mul]
    exact hTD.mul_right hTU
  · rw [map_mul, map_mul]
    exact (hTU.mul_right hTD).mul_right hTU

def rev7Perm : Equiv.Perm (Fin 7) := Equiv.swap 0 5 * Equiv.swap 1 4 * Equiv.swap 2 3

theorem rev7Perm_symm : rev7Perm.symm = rev7Perm := by decide

def rev7 : SL(7, ZMod 2) :=
  ⟨rev7Perm.permMatrix (ZMod 2), by
    rw [Matrix.det_permutation, rev7Perm, Equiv.Perm.sign_mul, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide),
      Equiv.Perm.sign_swap (by decide)]
    decide⟩

theorem rev7_mul_self : rev7 * rev7 = 1 := by
  apply Subtype.ext
  change rev7Perm.permMatrix (ZMod 2) * rev7Perm.permMatrix (ZMod 2) = 1
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul, PEquiv.toMatrix_toPEquiv_eq,
    Matrix.submatrix_submatrix]
  ext a b
  fin_cases a <;> fin_cases b <;> rfl

theorem coe_rev7_conj (M : Matrix (Fin 7) (Fin 7) (ZMod 2)) :
    (rev7 : Matrix (Fin 7) (Fin 7) (ZMod 2)) * M * (rev7 : Matrix (Fin 7) (Fin 7) (ZMod 2)) =
      M.submatrix rev7Perm rev7Perm := by
  change rev7Perm.permMatrix (ZMod 2) * M * rev7Perm.permMatrix (ZMod 2) = _
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv,
    Matrix.submatrix_submatrix, rev7Perm_symm]
  rfl

def swapConj (A : SL(2, ZMod 2)) : SL(2, ZMod 2) :=
  ⟨(A : Matrix (Fin 2) (Fin 2) (ZMod 2)).submatrix (Equiv.swap 0 1) (Equiv.swap 0 1), by
    rw [Matrix.det_submatrix_equiv_self]
    exact A.2⟩

theorem blockMat_submatrix_rev7 (k : ℕ) (hk : k = 2 ∨ k = 3 ∨ k = 4)
    (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) :
    (blockMat 7 k A).submatrix rev7Perm rev7Perm =
      blockMat 7 (4 - k) (A.submatrix (Equiv.swap 0 1) (Equiv.swap 0 1)) := by
  rcases hk with rfl | rfl | rfl <;>
  · ext a b
    fin_cases a <;> fin_cases b <;>
      simp [blockMat_apply, rev7Perm, Equiv.swap_apply_def]

theorem rev7_conj_block (k : Fin 6) (hk : (k : ℕ) = 2 ∨ (k : ℕ) = 3 ∨ (k : ℕ) = 4)
    (A : SL(2, ZMod 2)) :
    rev7 * blockSL2 (ZMod 2) 6 k A * rev7 =
      blockSL2 (ZMod 2) 6 ⟨4 - k, by omega⟩ (swapConj A) := by
  apply Subtype.ext
  change (rev7 : Matrix (Fin 7) (Fin 7) (ZMod 2)) * blockMat 7 (k : ℕ)
      (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) * (rev7 : Matrix (Fin 7) (Fin 7) (ZMod 2)) =
    blockMat 7 (4 - (k : ℕ))
      ((A : Matrix (Fin 2) (Fin 2) (ZMod 2)).submatrix (Equiv.swap 0 1) (Equiv.swap 0 1))
  rw [coe_rev7_conj]
  exact blockMat_submatrix_rev7 k hk A

theorem swapConj_swapConj (A : SL(2, ZMod 2)) : swapConj (swapConj A) = A := by
  apply Subtype.ext
  ext a b
  fin_cases a <;> fin_cases b <;> simp [swapConj]

theorem map_rev7_range_block (k : Fin 6) (hk : (k : ℕ) = 2 ∨ (k : ℕ) = 3 ∨ (k : ℕ) = 4) :
    (blockSL2 (ZMod 2) 6 k).range.map (MulAut.conj rev7).toMonoidHom =
      (blockSL2 (ZMod 2) 6 ⟨4 - k, by omega⟩).range := by
  have hinv : rev7⁻¹ = rev7 := inv_eq_of_mul_eq_one_right rev7_mul_self
  ext x
  simp only [Subgroup.mem_map, MonoidHom.mem_range, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    hinv]
  constructor
  · rintro ⟨_, ⟨A, rfl⟩, rfl⟩
    exact ⟨swapConj A, (rev7_conj_block k hk A).symm⟩
  · rintro ⟨B, rfl⟩
    refine ⟨_, ⟨swapConj B, rfl⟩, ?_⟩
    rw [rev7_conj_block k hk, swapConj_swapConj]

def swap3 : SL(3, ZMod 2) :=
  ⟨(Equiv.swap (0 : Fin 3) 2).permMatrix (ZMod 2), by
    rw [Matrix.det_permutation, Equiv.Perm.sign_swap (by decide)]
    decide⟩

theorem swap3_mul_self : swap3 * swap3 = 1 := by
  apply Subtype.ext
  change (Equiv.swap (0 : Fin 3) 2).permMatrix (ZMod 2) *
    (Equiv.swap (0 : Fin 3) 2).permMatrix (ZMod 2) = 1
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul, PEquiv.toMatrix_toPEquiv_eq,
    Matrix.submatrix_submatrix]
  ext a b
  fin_cases a <;> fin_cases b <;> rfl

theorem swap3_conj_B12 (A : SL(2, ZMod 2)) :
    swap3 * blockSL (ZMod 2) 3 2 0 (by omega) A * swap3 =
      blockSL (ZMod 2) 3 2 1 (by omega) (swapConj A) := by
  apply Subtype.ext
  change (Equiv.swap (0 : Fin 3) 2).permMatrix (ZMod 2) * blockMat 3 0
      (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) * (Equiv.swap (0 : Fin 3) 2).permMatrix (ZMod 2) =
    blockMat 3 1
      ((A : Matrix (Fin 2) (Fin 2) (ZMod 2)).submatrix (Equiv.swap 0 1) (Equiv.swap 0 1))
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv,
    Matrix.submatrix_submatrix, Equiv.symm_swap]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [blockMat_apply, Equiv.swap_apply_def]

theorem map_swap3_B12 : (B12 (ZMod 2)).map (MulAut.conj swap3).toMonoidHom = B23 (ZMod 2) := by
  have hinv : swap3⁻¹ = swap3 := inv_eq_of_mul_eq_one_right swap3_mul_self
  ext x
  simp only [B12, B23, Subgroup.mem_map, MonoidHom.mem_range, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, hinv]
  constructor
  · rintro ⟨_, ⟨A, rfl⟩, rfl⟩
    exact ⟨swapConj A, (swap3_conj_B12 A).symm⟩
  · rintro ⟨B, rfl⟩
    refine ⟨_, ⟨swapConj B, rfl⟩, ?_⟩
    rw [swap3_conj_B12, swapConj_swapConj]

theorem map_swap3_B23 : (B23 (ZMod 2)).map (MulAut.conj swap3).toMonoidHom = B12 (ZMod 2) := by
  have hinv : swap3⁻¹ = swap3 := inv_eq_of_mul_eq_one_right swap3_mul_self
  have hid : (MulAut.conj swap3).toMonoidHom.comp (MulAut.conj swap3).toMonoidHom =
      MonoidHom.id SL(3, ZMod 2) := by
    ext1 x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MonoidHom.id_apply, hinv, ← mul_assoc, swap3_mul_self, one_mul]
    rw [mul_assoc, swap3_mul_self, mul_one]
  rw [← map_swap3_B12, Subgroup.map_map, hid, Subgroup.map_id]

end CFSG.StandardType.FF81.Blocks
