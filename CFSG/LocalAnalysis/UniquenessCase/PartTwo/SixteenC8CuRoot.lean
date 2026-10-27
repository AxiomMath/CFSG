module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8CuGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.SpCurtis

open Matrix

theorem xE_mul_self (s : Fin 3) : xE s * xE s = 1 := by
  apply gM_injective
  show toMat (xB s) * toMat (xB s) = 1
  rw [← toMat_bmul, (bit_invol s).1, toMat_bone]

theorem yE_mul_self (s : Fin 3) : yE s * yE s = 1 := by
  apply gM_injective
  show toMat (yB s) * toMat (yB s) = 1
  rw [← toMat_bmul, (bit_invol s).2.1, toMat_bone]

theorem sE_mul_self (s : Fin 3) : sE s * sE s = 1 := by
  apply gM_injective
  show toMat (sB s) * toMat (sB s) = 1
  rw [← toMat_bmul, (bit_invol s).2.2, toMat_bone]

theorem xE_mul_yE (s : Fin 3) : xE s * yE s = yE s * sE s := by
  apply gM_injective
  show toMat (xB s) * toMat (yB s) = toMat (yB s) * toMat (sB s)
  rw [← toMat_bmul, ← toMat_bmul, (bit_rel s).2.2.1]

theorem xE_mul_yE' (s : Fin 3) : xE s * yE s = sE s * xE s := by
  apply gM_injective
  show toMat (xB s) * toMat (yB s) = toMat (sB s) * toMat (xB s)
  rw [← toMat_bmul, ← toMat_bmul, (bit_rel s).2.2.2.1]

theorem xE_eq_ysy (s : Fin 3) : xE s = yE s * sE s * yE s := by
  apply gM_injective
  show toMat (xB s) = toMat (yB s) * toMat (sB s) * toMat (yB s)
  rw [← toMat_bmul, ← toMat_bmul, ← (bit_rel s).2.2.2.2.1]

theorem xE_inv (s : Fin 3) : (xE s)⁻¹ = xE s := inv_eq_of_mul_eq_one_right (xE_mul_self s)

theorem yE_inv (s : Fin 3) : (yE s)⁻¹ = yE s := inv_eq_of_mul_eq_one_right (yE_mul_self s)

@[expose] def qRow : Fin 3 → Fin 6 := ![0, 1, 2]

@[expose] def qCol : Fin 3 → Fin 6 := ![1, 2, 3]

@[expose] def IsQs (s : Fin 3) (M : Matrix (Fin 6) (Fin 6) (ZMod 2)) : Prop :=
  IsUpU M ∧ M (qRow s) (qCol s) = 0

@[expose] def IsQm (s : Fin 3) (M : Matrix (Fin 6) (Fin 6) (ZMod 2)) : Prop :=
  IsLoU M ∧ M (qCol s) (qRow s) = 0

instance (s : Fin 3) (M : Matrix (Fin 6) (Fin 6) (ZMod 2)) : Decidable (IsQs s M) := by
  unfold IsQs
  infer_instance

instance (s : Fin 3) (M : Matrix (Fin 6) (Fin 6) (ZMod 2)) : Decidable (IsQm s M) := by
  unfold IsQm
  infer_instance

theorem xM_mul_apply (s : Fin 3) (M : Matrix (Fin 6) (Fin 6) (ZMod 2)) :
    (xM s * M) (qRow s) (qCol s) = M (qRow s) (qCol s) + M (qCol s) (qCol s) := by
  fin_cases s <;>
    simp [qRow, qCol, xM_eq_toMat, xB, toMat, mul_apply, Fin.sum_univ_six, Nat.testBit] <;> ring

theorem yM_mul_apply (s : Fin 3) (M : Matrix (Fin 6) (Fin 6) (ZMod 2)) :
    (yM s * M) (qCol s) (qRow s) = M (qCol s) (qRow s) + M (qRow s) (qRow s) := by
  fin_cases s <;>
    simp [qRow, qCol, yM_eq_toMat, yB, toMat, mul_apply, Fin.sum_univ_six, Nat.testBit] <;> ring

theorem xM_mul_apply_diag (s : Fin 3) (M : Matrix (Fin 6) (Fin 6) (ZMod 2)) :
    (xM s * M) (qRow s) (qRow s) = M (qRow s) (qRow s) + M (qCol s) (qRow s) := by
  fin_cases s <;>
    simp [qRow, qCol, xM_eq_toMat, xB, toMat, mul_apply, Fin.sum_univ_six, Nat.testBit] <;> ring

theorem yM_mul_apply_diag (s : Fin 3) (M : Matrix (Fin 6) (Fin 6) (ZMod 2)) :
    (yM s * M) (qCol s) (qCol s) = M (qCol s) (qCol s) + M (qRow s) (qCol s) := by
  fin_cases s <;>
    simp [qRow, qCol, yM_eq_toMat, yB, toMat, mul_apply, Fin.sum_univ_six, Nat.testBit] <;> ring

theorem mul_xM_apply (s : Fin 3) (N : Matrix (Fin 6) (Fin 6) (ZMod 2)) :
    (N * xM s) (qRow s) (qCol s) = N (qRow s) (qCol s) + N (qRow s) (qRow s) := by
  fin_cases s <;>
    simp [qRow, qCol, xM_eq_toMat, xB, toMat, mul_apply, Fin.sum_univ_six, Nat.testBit] <;> ring

theorem mul_yM_apply (s : Fin 3) (N : Matrix (Fin 6) (Fin 6) (ZMod 2)) :
    (N * yM s) (qCol s) (qRow s) = N (qCol s) (qRow s) + N (qCol s) (qCol s) := by
  fin_cases s <;>
    simp [qRow, qCol, yM_eq_toMat, yB, toMat, mul_apply, Fin.sum_univ_six, Nat.testBit] <;> ring

theorem decomp_up {s : Fin 3} {M : Matrix (Fin 6) (Fin 6) (ZMod 2)} (hM : IsUpU M) :
    IsQs s M ∨ IsQs s (xM s * M) := by
  by_cases h : M (qRow s) (qCol s) = 0
  · exact Or.inl ⟨hM, h⟩
  · refine Or.inr ⟨upU_mul (xE_upU s) hM, ?_⟩
    have h1 : M (qRow s) (qCol s) = 1 := (by decide : ∀ x : ZMod 2, x ≠ 0 → x = 1) _ h
    rw [xM_mul_apply, h1, (hM (qCol s) (qCol s)).2 rfl]
    decide

theorem decomp_lo {s : Fin 3} {M : Matrix (Fin 6) (Fin 6) (ZMod 2)} (hM : IsLoU M) :
    IsQm s M ∨ IsQm s (yM s * M) := by
  by_cases h : M (qCol s) (qRow s) = 0
  · exact Or.inl ⟨hM, h⟩
  · refine Or.inr ⟨loU_mul (yE_loU s) hM, ?_⟩
    have h1 : M (qCol s) (qRow s) = 1 := (by decide : ∀ x : ZMod 2, x ≠ 0 → x = 1) _ h
    rw [yM_mul_apply, h1, (hM (qRow s) (qRow s)).2 rfl]
    decide

theorem Qs_conj_x {s : Fin 3} {q : G6} (h : IsQs s (gM q)) : IsQs s (gM (xE s * q * xE s)) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨upU_mul (upU_mul (xE_upU s) h1) (xE_upU s), ?_⟩
  change (xM s * gM q * xM s) (qRow s) (qCol s) = 0
  have hd1 : gM q (qCol s) (qCol s) = 1 := (h1 _ _).2 rfl
  have hd2 : gM q (qRow s) (qRow s) = 1 := (h1 _ _).2 rfl
  have hl : gM q (qCol s) (qRow s) = 0 := (h1 _ _).1 (by fin_cases s <;> decide)
  rw [mul_xM_apply, xM_mul_apply, xM_mul_apply_diag, h2, hd1, hd2, hl]
  decide

theorem Qm_conj_y {s : Fin 3} {q : G6} (h : IsQm s (gM q)) : IsQm s (gM (yE s * q * yE s)) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨loU_mul (loU_mul (yE_loU s) h1) (yE_loU s), ?_⟩
  change (yM s * gM q * yM s) (qCol s) (qRow s) = 0
  have hd1 : gM q (qCol s) (qCol s) = 1 := (h1 _ _).2 rfl
  have hd2 : gM q (qRow s) (qRow s) = 1 := (h1 _ _).2 rfl
  have hl : gM q (qRow s) (qCol s) = 0 := (h1 _ _).1 (by fin_cases s <;> decide)
  rw [mul_yM_apply, yM_mul_apply, yM_mul_apply_diag, h2, hd1, hd2, hl]
  decide

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.SpCurtis
