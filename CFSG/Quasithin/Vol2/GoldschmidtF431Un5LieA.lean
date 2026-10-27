module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieDefs
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModU5Stab
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsU5Base
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3FusionLevi
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3FusionModel

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.LocalAnalysis.EvenBN.U5 CFSG.Quasithin.H13.Sec53F.Unit

section Mat

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem mat_z₁SU_eq : mat (z₁SU h) = 1 + Matrix.single ιe₁ ιf₁ (1 : K) := by
  rw [z₁SU, mat_vSU]
  ext a b
  rcases hypIndex_cases a with rfl | rfl | rfl | rfl | rfl <;>
    rcases hypIndex_cases b with rfl | rfl | rfl | rfl | rfl <;>
    simp [oddUni, ιe₁, ιe₂, ιz, ιf₁, ιf₂]

theorem mat_z₂SU_eq :
    mat (z₂SU h) = 1 + (Matrix.single ιe₁ ιf₂ (1 : K) + Matrix.single ιe₂ ιf₁ 1) := by
  rw [z₂SU, mat_vSU]
  ext a b
  rcases hypIndex_cases a with rfl | rfl | rfl | rfl | rfl <;>
    rcases hypIndex_cases b with rfl | rfl | rfl | rfl | rfl <;>
    simp [oddUni, ιe₁, ιe₂, ιz, ιf₁, ιf₂]

theorem Yof_z₁SU : Yof (z₁SU h) = !![1, 0; 0, 0] := Yof_eq (mat_vSU _)

theorem Yof_z₂SU : Yof (z₂SU h) = !![0, 1; 1, 0] := Yof_eq (mat_vSU _)

end Mat

section Cls

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem exists_lev_conj_of_det_eq_zero {v w : hypSU h 2 1} (hv : v ∈ Vsub h) (hw : w ∈ Vsub h)
    (hv0 : Yof v ≠ 0) (hvd : (Yof v).det = 0) (hw0 : Yof w ≠ 0) (hwd : (Yof w).det = 0) :
    ∃ (A : Matrix (Fin 2) (Fin 2) K) (hA : IsUnit A.det),
      lev (hK := h) A hA * v * (lev (hK := h) A hA)⁻¹ = w := by
  obtain ⟨A, hA, hAY⟩ := exists_conj_eq_of_det_eq_zero h (herm_Yof hv) hv0 hvd (herm_Yof hw) hw0
    hwd
  obtain ⟨hmem, hY⟩ := lev_conj_Yof h A hA hv
  exact ⟨A, hA, Yof_injOn h hmem hw (by rw [hY, hAY])⟩

theorem exists_lev_conj_of_det_ne_zero {v w : hypSU h 2 1} (hv : v ∈ Vsub h) (hw : w ∈ Vsub h)
    (hvd : (Yof v).det ≠ 0) (hwd : (Yof w).det ≠ 0) :
    ∃ (A : Matrix (Fin 2) (Fin 2) K) (hA : IsUnit A.det),
      lev (hK := h) A hA * v * (lev (hK := h) A hA)⁻¹ = w := by
  obtain ⟨A, hA, hAY⟩ := exists_conj_eq_of_det_ne_zero h (herm_Yof hv) hvd (herm_Yof hw) hwd
  obtain ⟨hmem, hY⟩ := lev_conj_Yof h A hA hv
  exact ⟨A, hA, Yof_injOn h hmem hw (by rw [hY, hAY])⟩

theorem isConj_proj_of_conj {x : hypPSU h 2 1} {v w c : hypSU h 2 1} {d : hypPSU h 2 1}
    (hvx : hypProj h 2 1 v = d⁻¹ * x * d) (hcw : c * v * c⁻¹ = w) :
    IsConj (hypProj h 2 1 w) x := by
  rw [isConj_comm, isConj_iff]
  refine ⟨hypProj h 2 1 c * d⁻¹, ?_⟩
  rw [← hcw, map_mul, map_mul, map_inv, hvx]
  group

theorem cls_Y (hf : 2 ≤ f) {x : hypPSU h 2 1} (hx : orderOf x = 2) :
    IsConj (z5Y h) x ∨ IsConj (t5Y h) x := by
  have hxx : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx, sq] at this
  obtain ⟨d, v, hv, hvx⟩ := involutionsConjIntoV h hf (u5_center_eq_bot h) x hxx
  have hv1 : v ≠ 1 := by
    rintro rfl
    have h1 : x = 1 := by
      have := congrArg (fun y => d * y * d⁻¹) hvx
      simp only [map_one, mul_assoc, mul_inv_cancel, mul_one] at this
      simpa [mul_assoc] using this.symm
    rw [h1, orderOf_one] at hx
    exact absurd hx (by norm_num)
  have hY0 : Yof v ≠ 0 := fun h0 => hv1 ((eq_one_iff_Yof_eq_zero h hv).2 h0)
  have hz1 : z₁SU h ∈ Vsub h := vSU_mem_Vsub (isHerm_e₁₁ h)
  have hz2 : z₂SU h ∈ Vsub h := vSU_mem_Vsub (isHerm_swap h)
  by_cases hd : (Yof v).det = 0
  · left
    have hz10 : Yof (z₁SU h) ≠ 0 := by
      rw [Yof_z₁SU]
      intro e
      have := congrFun (congrFun e 0) 0
      simp at this
    obtain ⟨A, hA, hAv⟩ := exists_lev_conj_of_det_eq_zero hv hz1 hY0 hd hz10
      (by rw [Yof_z₁SU]; simp)
    exact isConj_proj_of_conj hvx hAv
  · right
    obtain ⟨A, hA, hAv⟩ := exists_lev_conj_of_det_ne_zero hv hz2 hd
      (by
        rw [Yof_z₂SU, Matrix.det_fin_two_of]
        simp)
    exact isConj_proj_of_conj hvx hAv

end Cls

section Noconj

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem single_mul_mul_single_one (X : Matrix (HypIndex 2 1) (HypIndex 2 1) K) :
    Matrix.single ιe₁ ιf₁ (1 : K) * X * Matrix.single ιe₁ ιf₁ 1 =
      X ιf₁ ιe₁ • Matrix.single ιe₁ ιf₁ (1 : K) := by
  rw [Matrix.single_mul_mul_single, Matrix.smul_single]
  simp

theorem map_one_add_single {σ : K ≃+* K} (i j : HypIndex 2 1) :
    ((1 : Matrix (HypIndex 2 1) (HypIndex 2 1) K) + Matrix.single i j 1).map σ =
      1 + Matrix.single i j 1 := by
  ext a b
  by_cases hab : a = b <;> by_cases hi : i = a <;> by_cases hj : j = b <;>
    simp [Matrix.single_apply, hab, hi, hj]

theorem map_one_add_single_add {σ : K ≃+* K} (i j k l : HypIndex 2 1) :
    ((1 : Matrix (HypIndex 2 1) (HypIndex 2 1) K) +
      (Matrix.single i j 1 + Matrix.single k l 1)).map σ =
      1 + (Matrix.single i j 1 + Matrix.single k l 1) := by
  ext a b
  by_cases hab : a = b <;> by_cases hi : i = a <;> by_cases hj : j = b <;>
    by_cases hk : k = a <;> by_cases hl : l = b <;>
    simp [Matrix.single_apply, hab, hi, hj, hk, hl]

theorem noconj_Y (φ : MulAut (hypPSU h 2 1)) : φ (z5Y h) ≠ t5Y h := by
  intro hφ
  obtain ⟨x, rfl⟩ := Phi_surjective h φ
  have e1 : hypProj h 2 1 (act h x (z₁SU h)) = hypProj h 2 1 (z₂SU h) := by
    rw [← Phi_apply]
    exact hφ
  have hsq1 : z₁SU h * z₁SU h = 1 := Vsub_sq (vSU_mem_Vsub (isHerm_e₁₁ h))
  have hsq2 : z₂SU h * z₂SU h = 1 := Vsub_sq (vSU_mem_Vsub (isHerm_swap h))
  have hg : act h x (z₁SU h) * act h x (z₁SU h) = 1 := by rw [← act_mul, hsq1, act_one]
  have heq : act h x (z₁SU h) = z₂SU h :=
    eq_of_innM_eq_of_sq (u5_center_eq_bot h) (MulEquiv.ext fun y => by simp [innM_apply, e1]) hg
      hsq2
  have hL := lmat_mul_map x (z₁SU h)
  rw [heq, mat_z₁SU_eq, mat_z₂SU_eq, map_one_add_single] at hL
  set N₁ : Matrix (HypIndex 2 1) (HypIndex 2 1) K := Matrix.single ιe₁ ιf₁ 1 with hN₁
  set N₂ : Matrix (HypIndex 2 1) (HypIndex 2 1) K :=
    Matrix.single ιe₁ ιf₂ 1 + Matrix.single ιe₂ ιf₁ 1 with hN₂
  set L := lmat x with hLdef
  set Li : Matrix (HypIndex 2 1) (HypIndex 2 1) K :=
    ((x.1.left⁻¹ : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) with hLi
  have hLiL : Li * L = 1 := by rw [hLi, hLdef, lmat, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hLLi : L * Li = 1 := by rw [hLi, hLdef, lmat, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hL' : L * N₁ = N₂ * L := by
    rw [mul_add, add_mul, mul_one, one_mul] at hL
    exact add_left_cancel hL
  have hN : N₂ = L * N₁ * Li := by
    calc N₂ = N₂ * (L * Li) := by rw [hLLi, mul_one]
      _ = L * N₁ * Li := by rw [← mul_assoc, ← hL']
  have key : ∀ X : Matrix (HypIndex 2 1) (HypIndex 2 1) K,
      N₂ * X * N₂ = (Li * X * L) ιf₁ ιe₁ • N₂ := by
    intro X
    have h1 : N₂ * X * N₂ = L * (N₁ * (Li * X * L) * N₁) * Li := by
      conv_lhs => rw [hN]
      simp only [Matrix.mul_assoc]
    rw [h1, hN₁, single_mul_mul_single_one, Matrix.mul_smul, Matrix.smul_mul, ← hN₁, ← hN]
  have hX := key (Matrix.single ιf₂ ιe₁ 1)
  have e2 : N₂ * Matrix.single ιf₂ ιe₁ 1 * N₂ = Matrix.single ιe₁ ιf₂ 1 := by
    rw [hN₂]
    simp [add_mul, mul_add, Matrix.single_mul_single_of_ne, ιe₁, ιe₂, ιf₁, ιf₂]
  rw [e2] at hX
  have h1 := congrFun (congrFun hX ιe₁) ιf₂
  have h2 := congrFun (congrFun hX ιe₂) ιf₁
  simp [hN₂, ιe₁, ιe₂, ιf₁, ιf₂] at h1 h2
  exact one_ne_zero (h1.trans h2.symm)

end Noconj

end CFSG.Quasithin.H13.F431.Un
