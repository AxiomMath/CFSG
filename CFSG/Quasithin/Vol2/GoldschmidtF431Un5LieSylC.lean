module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieSylB

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.L5

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.U5K.Hyp
  CFSG.LocalAnalysis.EvenBN.U5 CFSG.LocalAnalysis.ComponentInitial

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem syl_decomp {g : hypSU h 2 1}
    (hze : ∀ i, mat g (.inr (.inl 0)) (.inl i) = 0)
    (hfe : ∀ j i, mat g (.inr (.inr j)) (.inl i) = 0)
    (hfz : ∀ j, mat g (.inr (.inr j)) (.inr (.inl 0)) = 0) :
    ∃ (A C : Matrix (Fin 2) (Fin 2) K) (x : Fin 2 → K) (d : K), IsUnit A.det ∧
      C + (C.map h.bar)ᵀ = -vecMulVec x (fun j => h.bar (x j)) ∧
      d = h.bar A.det / A.det ∧ A = blkA (mat g) ∧ blkD (mat g) = barInvT h A ∧
      mat g = oddDiag h A d * oddUni h x C := by
  obtain ⟨M, hMg⟩ : ∃ M, mat g = M := ⟨_, rfl⟩
  have hM : M = blk3 (blkA M) (blkX M) (blkY M) (blkP M) (blkQ M) (blkD M) := by
    ext a b
    rcases a with i | k | i <;> rcases b with j | l | j
    · rfl
    · rfl
    · rfl
    · rw [Subsingleton.elim k 0, ← hMg, hze]; rfl
    · rfl
    · rfl
    · rw [← hMg, hfe]; rfl
    · rw [Subsingleton.elim l 0, ← hMg, hfz]; rfl
    · rfl
  have hgram := (mem_hypSU.mp g.2).1
  have hdetM := (mem_hypSU.mp g.2).2
  change ((mat g).map h.bar)ᵀ * hypGram 2 1 K * mat g = hypGram 2 1 K at hgram
  change (mat g).det = 1 at hdetM
  rw [hMg, hM] at hgram hdetM
  obtain ⟨h1, h2, h3, h4⟩ := (blk3_gram_iff h _ _ _ _ _ _).mp hgram
  have hdet := isUnit_det_of_mul_eq_one h1
  have hD := eq_barInvT_of_mul_eq_one h1
  set d := blkP M 0 0 with hd
  have hP : blkP M = of fun _ _ => d := by
    ext k l
    rw [Subsingleton.elim k 0, Subsingleton.elim l 0]
    rfl
  have hdd : h.bar d * d = 1 := by
    have := congrFun (congrFun h2 0) 0
    simpa [mul_apply, hP] using this
  set x : Fin 2 → K := fun i => ((blkA M)⁻¹ * blkX M) i 0 with hx
  have hX : blkX M = blkA M * replicateCol (Fin 1) x := by
    have : replicateCol (Fin 1) x = (blkA M)⁻¹ * blkX M := by
      ext i k
      rw [Subsingleton.elim k 0]
      rfl
    rw [this, mul_nonsing_inv_cancel_left _ _ hdet]
  set C := (blkA M)⁻¹ * blkY M with hC
  have hY : blkY M = blkA M * C := by rw [hC, mul_nonsing_inv_cancel_left _ _ hdet]
  have hQ : blkQ M = of fun _ j => -d * h.bar (x j) := by
    rw [hX, hD, conjTranspose_mul', Matrix.mul_assoc, conjTranspose_mul_barInvT hdet,
      Matrix.mul_one, hP] at h3
    ext k j
    rw [Subsingleton.elim k 0]
    have := congrFun (congrFun h3 0) j
    simp only [Matrix.add_apply, mul_apply, transpose_apply, map_apply, replicateCol_apply,
      of_apply, Finset.univ_unique, Finset.sum_singleton, Matrix.zero_apply] at this
    rw [of_apply]
    linear_combination d * this - blkQ M 0 j * hdd
  refine ⟨blkA M, C, x, d, hdet, ?_, ?_, by rw [hMg], by rw [hMg]; exact hD, ?_⟩
  · rw [hY, hD, hQ, conjTranspose_mul', Matrix.mul_assoc, conjTranspose_mul_barInvT hdet,
      Matrix.mul_one, ← Matrix.mul_assoc, conjTranspose_barInvT_mul hdet, Matrix.one_mul,
      conjTranspose_row_mul_row x d hdd] at h4
    rw [eq_neg_iff_add_eq_zero, ← h4]
    abel
  · rw [det_blk3, hP, det_fin_one, of_apply, hD, det_barInvT hdet] at hdetM
    have h0 : (blkA M).det ≠ 0 := hdet.ne_zero
    have h0' : h.bar (blkA M).det ≠ 0 := (map_ne_zero h.bar).mpr h0
    field_simp at hdetM
    field_simp
    linear_combination hdetM
  · rw [hMg, oddDiag_mul_oddUni]
    conv_lhs => rw [hM]
    rw [← hX, ← hY, hP, hQ, hD]

theorem syl_decomp_of_comm {g : hypSU h 2 1} (hg : g * z₂SU h = z₂SU h * g) :
    ∃ (A C : Matrix (Fin 2) (Fin 2) K) (x : Fin 2 → K) (d : K), IsUnit A.det ∧
      C + (C.map h.bar)ᵀ = -vecMulVec x (fun j => h.bar (x j)) ∧
      d = h.bar A.det / A.det ∧ A = blkA (mat g) ∧
      A * !![0, 1; 1, 0] * (A.map h.bar)ᵀ = !![0, 1; 1, 0] ∧
      mat g = oddDiag h A d * oddUni h x C := by
  obtain ⟨A, C, x, d, hAu, hC, hd, hA, hD, hmat⟩ :=
    syl_decomp (syl_comm_z_e hg) (syl_comm_f_e hg) (syl_comm_f_z hg)
  refine ⟨A, C, x, d, hAu, hC, hd, hA, ?_, hmat⟩
  have e := syl_comm_AJ hg
  rw [← hA, hD] at e
  rw [e, Matrix.mul_assoc, mul_eq_one_comm.mp (conjTranspose_mul_barInvT hAu), Matrix.mul_one]

end CFSG.Quasithin.H13.F431.Un.L5
