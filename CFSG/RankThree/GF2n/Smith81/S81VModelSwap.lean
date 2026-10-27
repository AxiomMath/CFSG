module

public import CFSG.RankThree.GF2n.Smith81.S81VModelTorus

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.RankThree.GF2n.Smith81.U6Cube Module Matrix

variable {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F} {a b : Fin 3 → Fin 6 → F} {K : Type} [Field K]

@[expose] def swapM (F : Type) [Field F] : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F :=
  (Equiv.swap (Sum.inl (0 : Fin 3)) (Sum.inr (0 : Fin 3))).permMatrix F

private theorem swapM_apply (p q : Fin 3 ⊕ Fin 3) :
    swapM F p q = if q = Equiv.swap (Sum.inl (0 : Fin 3)) (Sum.inr (0 : Fin 3)) p then 1 else 0 := by
  simp only [swapM, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_apply, Pi.single_apply]

private theorem swapM_conj (M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) :
    swapM F * M * swapM F = M.submatrix (Equiv.swap (Sum.inl (0 : Fin 3)) (Sum.inr (0 : Fin 3)))
      (Equiv.swap (Sum.inl (0 : Fin 3)) (Sum.inr (0 : Fin 3))) := by
  unfold swapM Equiv.Perm.permMatrix
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Equiv.symm_swap]
  rfl

private theorem swapM_conj_apply (M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) (p q : Fin 3 ⊕ Fin 3) :
    (swapM F * M * swapM F) p q = M (Equiv.swap (Sum.inl (0 : Fin 3)) (Sum.inr (0 : Fin 3)) p)
      (Equiv.swap (Sum.inl (0 : Fin 3)) (Sum.inr (0 : Fin 3)) q) := by
  rw [swapM_conj, Matrix.submatrix_apply]

private theorem cT_swapM : cT σ (swapM F) = swapM F := by
  ext p q
  rw [cT_apply, swapM_apply, swapM_apply]
  by_cases h : q = Equiv.swap (Sum.inl (0 : Fin 3)) (Sum.inr (0 : Fin 3)) p
  · have h' : p = Equiv.swap (Sum.inl (0 : Fin 3)) (Sum.inr (0 : Fin 3)) q := by
      rw [h, Equiv.swap_apply_self]
    rw [if_pos h', if_pos h, map_one]
  · have h' : ¬ p = Equiv.swap (Sum.inl (0 : Fin 3)) (Sum.inr (0 : Fin 3)) q := by
      intro h''
      apply h
      rw [h'', Equiv.swap_apply_self]
    rw [if_neg h', if_neg h, map_zero]

theorem swapM_unitary : cT σ (swapM F) * Jm F * swapM F = Jm F := by
  rw [cT_swapM, swapM_conj]
  ext p q
  rcases p with i | i <;> rcases q with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Jm, Equiv.swap_apply_def]

theorem swapM_det : (swapM F).det = 1 := by
  have hne : (Sum.inl (0 : Fin 3)) ≠ Sum.inr (0 : Fin 3) := by simp
  unfold swapM
  rw [Matrix.det_permutation, Equiv.Perm.sign_swap hne]
  simp [CharTwo.neg_eq]

theorem swapM_mul_self : swapM F * swapM F = 1 := by
  unfold swapM
  rw [← Matrix.permMatrix_mul, Equiv.swap_mul_self, Matrix.permMatrix_one]

private theorem swap_dmat_inv (c₀ : F) (hc : c₀ ≠ 0) (hσc : σ c₀ = c₀) :
    swapM F * Matrix.fromBlocks (dmat c₀) 0 0 (cT σ (dmat c₀))⁻¹ * swapM F *
      Matrix.fromBlocks (dmat c₀) 0 0 (cT σ (dmat c₀))⁻¹ = 1 := by
  have hcT : cT σ (dmat c₀) = dmat c₀ := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [cT_apply, dmat, hσc]
  have hinv : (cT σ (dmat c₀))⁻¹ = Matrix.diagonal ![c₀⁻¹, 1, 1] := by
    apply Matrix.inv_eq_right_inv
    rw [hcT]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [dmat, hc]
  have hD : Matrix.fromBlocks (dmat c₀) 0 0 (cT σ (dmat c₀))⁻¹ =
      Matrix.diagonal (Sum.elim ![c₀, 1, 1] ![c₀⁻¹, 1, 1]) := by
    rw [hinv, dmat, Matrix.fromBlocks_diagonal]
  have hkey : ∀ p : Fin 3 ⊕ Fin 3,
      Sum.elim ![c₀, 1, 1] ![c₀⁻¹, 1, 1] (Equiv.swap (Sum.inl (0 : Fin 3)) (Sum.inr (0 : Fin 3)) p) *
        Sum.elim ![c₀, 1, 1] ![c₀⁻¹, 1, 1] p = 1 := by
    rintro (i | i) <;> fin_cases i <;> simp [Equiv.swap_apply_def, hc]
  rw [hD, swapM_conj, Matrix.submatrix_diagonal_equiv, Matrix.diagonal_mul_diagonal,
    ← Matrix.diagonal_one]
  congr 1
  funext p
  exact hkey p

private theorem swap_braid_mat :
    swapM F = Matrix.fromBlocks (1 : Matrix (Fin 3) (Fin 3) F) (Matrix.single 0 0 1) 0 1 *
      (swapM F * Matrix.fromBlocks (1 : Matrix (Fin 3) (Fin 3) F) (Matrix.single 0 0 1) 0 1 * swapM F) *
      Matrix.fromBlocks (1 : Matrix (Fin 3) (Fin 3) F) (Matrix.single 0 0 1) 0 1 := by
  have h2 : (1 : F) + 1 = 0 := CharTwo.add_self_eq_zero 1
  rw [swapM_conj]
  ext p q
  rcases p with i | i <;> rcases q with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_three, Matrix.single_apply,
      swapM_apply, Equiv.swap_apply_def, Matrix.one_apply, h2]

variable (hσ : ∀ c, σ (σ c) = c) (hf : Frame σ a b) (e₀ : K ≃+* Fσ σ)

include hσ hf

@[expose] noncomputable def sU : SUid σ 6 := ofGm hσ hf (swapM F) swapM_unitary swapM_det

theorem gm_sU : gm hσ hf (sU hσ hf) = swapM F :=
  gm_ofGm hσ hf _ _ _

theorem sU_sq : sU hσ hf * sU hσ hf = 1 := by
  apply gm_injective hσ hf
  rw [gm_mul, gm_sU, gm_one, swapM_mul_self]

theorem sU_dK (c : Kˣ) : sU hσ hf * dK hσ hf e₀ c * sU hσ hf = (dK hσ hf e₀ c)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  apply gm_injective hσ hf
  rw [gm_mul, gm_mul, gm_mul, gm_sU, gm_dK, gm_one]
  exact swap_dmat_inv ((e₀ (c : K) : Fσ σ) : F) (e₀_unit_ne_zero e₀ c) (e₀ (c : K)).2

theorem sU_braid : sU hσ hf =
    uK hσ hf ((1 : K) • n1K σ e₀) *
      (sU hσ hf * uK hσ hf ((1 : K) • n1K σ e₀) * sU hσ hf) * uK hσ hf ((1 : K) • n1K σ e₀) := by
  have hn : ((1 : K) • n1K σ e₀).mat = Matrix.single 0 0 1 := by
    simp [HermK.mat_smul, n1K_mat]
  apply gm_injective hσ hf
  rw [gm_mul, gm_mul, gm_mul, gm_mul, gm_sU, gm_uK, hn]
  exact swap_braid_mat

theorem ker_stab_U (H : HermK σ e₀) (h : tauK σ e₀ H = 0) :
    ∃ g : ↥(Pstab σ (Wa a)), (g : SUid σ 6) = sU hσ hf * uK hσ hf H * sU hσ hf := by
  have h00 : H.mat 0 0 = 0 := by
    have h1 := tauK_apply H
    rw [h, map_zero] at h1
    exact h1.symm
  have hmem : sU hσ hf * uK hσ hf H * sU hσ hf ∈ Pstab σ (Wa a) := by
    rw [mem_Pstab_iff hσ hf]
    intro i j
    rw [gm_mul, gm_mul, gm_sU, gm_uK, swapM_conj_apply]
    fin_cases i <;> fin_cases j <;>
      simp [Equiv.swap_apply_def, Matrix.one_apply, h00]
  exact ⟨⟨_, hmem⟩, rfl⟩

end CFSG.RankThree.GF2n.Smith81.S81V
