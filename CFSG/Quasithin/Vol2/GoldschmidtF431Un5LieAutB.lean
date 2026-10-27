module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieAutA
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieA

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.L5

set_option linter.unusedSectionVars false

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.LocalAnalysis.EvenBN.U5 CFSG.Quasithin.H13.Sec53F.Unit

section Act

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

@[expose] def Jm (K : Type) [Field K] : Matrix (Fin 2) (Fin 2) K := !![0, 1; 1, 0]

theorem Jm_mul_self : Jm K * Jm K = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Jm]

theorem trace_Jm_mul (M : Matrix (Fin 2) (Fin 2) K) : (Jm K * M).trace = M 1 0 + M 0 1 := by
  simp [Matrix.trace, Fin.sum_univ_two, Jm, Matrix.vecMul, dotProduct]

theorem trace_mul_Jm (M : Matrix (Fin 2) (Fin 2) K) : (M * Jm K).trace = M 0 1 + M 1 0 := by
  simp [Matrix.trace, Fin.sum_univ_two, Matrix.mul_apply, Jm]

theorem lmat_comm_nN (x : Gam h) (hx : act h x (z₂SU h) = z₂SU h) :
    lmat x * nN K = nN K * lmat x := by
  have hL := lmat_mul_map x (z₂SU h)
  rw [hx, mat_z₂SU_eq, map_one_add_single_add] at hL
  rw [nN]
  rw [mul_add, add_mul, mul_one, one_mul] at hL
  exact add_left_cancel hL

theorem act_z₂SU_eq (x : Gam h) (hφ : Phi h x (t5Y h) = t5Y h) : act h x (z₂SU h) = z₂SU h := by
  have e1 : hypProj h 2 1 (act h x (z₂SU h)) = hypProj h 2 1 (z₂SU h) := by
    rw [← Phi_apply]
    exact hφ
  have hsq2 : z₂SU h * z₂SU h = 1 := Vsub_sq (vSU_mem_Vsub (isHerm_swap h))
  have hg : act h x (z₂SU h) * act h x (z₂SU h) = 1 := by rw [← act_mul, hsq2, act_one]
  exact eq_of_innM_eq_of_sq (u5_center_eq_bot h) (MulEquiv.ext fun y => by simp [innM_apply, e1]) hg
    hsq2

variable (x : Gam h)

@[expose] def Aee : Matrix (Fin 2) (Fin 2) K := (lmat x).submatrix Sum.inl Sum.inl

variable {x}

theorem lmat_blocks (hc : lmat x * nN K = nN K * lmat x) :
    lmat x = blk3 (Aee x) ((lmat x).submatrix Sum.inl (Sum.inr ∘ Sum.inl))
      ((lmat x).submatrix Sum.inl (Sum.inr ∘ Sum.inr))
      ((lmat x).submatrix (Sum.inr ∘ Sum.inl) (Sum.inr ∘ Sum.inl))
      ((lmat x).submatrix (Sum.inr ∘ Sum.inl) (Sum.inr ∘ Sum.inr)) (Jm K * Aee x * Jm K) := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩ := blocks_of_comm hc
  have hD : (lmat x).submatrix (Sum.inr ∘ Sum.inr) (Sum.inr ∘ Sum.inr) = Jm K * Aee x * Jm K := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Aee, Jm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] <;>
      first | exact b9 | exact b10 | exact b11 | exact b12
  have := eq_blk3_of_vanish (lmat x)
    (fun k j => by fin_cases k; fin_cases j <;> first | exact b1 | exact b2)
    (fun i j => by
      fin_cases i <;> fin_cases j <;> first | exact b3 | exact b4 | exact b5 | exact b6)
    (fun i l => by fin_cases l; fin_cases i <;> first | exact b7 | exact b8)
  rwa [hD] at this

theorem Jm_mul_mul_self (M : Matrix (Fin 2) (Fin 2) K) : Jm K * (Jm K * M) = M := by
  rw [← Matrix.mul_assoc, Jm_mul_self, Matrix.one_mul]

theorem isUnit_det_Aee (hc : lmat x * nN K = nN K * lmat x) : IsUnit (Aee x).det := by
  have hL : IsUnit (lmat x).det := by
    have := (x.1.left : GL (HypIndex 2 1) K).isUnit
    exact (Matrix.isUnit_iff_isUnit_det _).1 this
  rw [lmat_blocks hc] at hL
  have hdet : ∀ (A : Matrix (Fin 2) (Fin 2) K) (X : Matrix (Fin 2) (Fin 1) K)
      (Yb : Matrix (Fin 2) (Fin 2) K) (P : Matrix (Fin 1) (Fin 1) K) (Q : Matrix (Fin 1) (Fin 2) K)
      (D : Matrix (Fin 2) (Fin 2) K), (blk3 A X Yb P Q D).det = A.det * (P.det * D.det) := by
    intro A X Yb P Q D
    rw [blk3, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₂₁]
  rw [hdet] at hL
  exact (IsUnit.mul_iff.1 hL).1

theorem Aee_inv_mul (hc : lmat x * nN K = nN K * lmat x) : (Aee x)⁻¹ * Aee x = 1 :=
  Matrix.nonsing_inv_mul _ (isUnit_det_Aee hc)

theorem Aee_mul_inv (hc : lmat x * nN K = nN K * lmat x) : Aee x * (Aee x)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (isUnit_det_Aee hc)

theorem exists_Ypp (hc : lmat x * nN K = nN K * lmat x) {Y' : Matrix (Fin 2) (Fin 2) K}
    (hY' : IsHerm h Y') :
    ∃ Y'' : Matrix (Fin 2) (Fin 2) K, mat (act h x (vSU h Y' hY')) = oddUni h 0 Y'' ∧
      Y'' = Aee x * Y'.map x.1.right * (Jm K * (Aee x)⁻¹ * Jm K) := by
  refine ⟨_, ?_, rfl⟩
  have h1 := Aee_inv_mul hc
  have hD : (Aee x * Y'.map x.1.right * (Jm K * (Aee x)⁻¹ * Jm K)) * (Jm K * Aee x * Jm K) =
      Aee x * Y'.map x.1.right := by
    have e : (Jm K * (Aee x)⁻¹ * Jm K) * (Jm K * Aee x * Jm K) = 1 := by
      calc (Jm K * (Aee x)⁻¹ * Jm K) * (Jm K * Aee x * Jm K)
          = Jm K * ((Aee x)⁻¹ * (Aee x * Jm K)) := by
            simp only [Matrix.mul_assoc, Jm_mul_mul_self]
        _ = 1 := by
            have e2 : (Aee x)⁻¹ * (Aee x * Jm K) = Jm K := by
              rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
            rw [e2, Jm_mul_self]
    rw [Matrix.mul_assoc, e, Matrix.mul_one]
  have hb := lmat_blocks hc
  set X := (lmat x).submatrix Sum.inl (Sum.inr ∘ Sum.inl) with hXdef
  set Yb := (lmat x).submatrix Sum.inl (Sum.inr ∘ Sum.inr) with hYbdef
  set P := (lmat x).submatrix (Sum.inr ∘ Sum.inl) (Sum.inr ∘ Sum.inl) with hPdef
  set Q := (lmat x).submatrix (Sum.inr ∘ Sum.inl) (Sum.inr ∘ Sum.inr) with hQdef
  have key := blk3_oddUni_comm (h := h) x.1.right (Aee x) X Yb P Q (Jm K * Aee x * Jm K) Y' _ hD
  rw [← hb] at key
  have hL := lmat_mul_map x (vSU h Y' hY')
  rw [mat_vSU] at hL
  set L := lmat x with hLdef
  set Li : Matrix (HypIndex 2 1) (HypIndex 2 1) K :=
    ((x.1.left⁻¹ : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) with hLi
  have hLLi : L * Li = 1 := by rw [hLi, hLdef, lmat, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  calc mat (act h x (vSU h Y' hY')) = mat (act h x (vSU h Y' hY')) * L * Li := by
        rw [Matrix.mul_assoc, hLLi, Matrix.mul_one]
    _ = _ := by rw [← hL, ← key, Matrix.mul_assoc, hLLi, Matrix.mul_one]

end Act

end CFSG.Quasithin.H13.F431.Un.L5
