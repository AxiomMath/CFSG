module

public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5GL2
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma41aU3

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG CFSG.ClassicalInvolution Matrix
open CFSG.ClassicalInvolution.Q3.TA3.Q5GL2 CFSG.LocalAnalysis.ComponentInitial
  CFSG.GH74.GLS.IVK.Proofs2
open scoped MatrixGroups

variable {K : Type} [Field K] {H : Subgroup (GL (Fin 2) K)}

theorem exists_sq_eq_mul_mem_slPart_center
    (hH : ∀ A : H,
      GeneralLinearGroup.scalar (Fin 2) (GeneralLinearGroup.det (A : GL (Fin 2) K)) ∈ H)
    (A : H) :
    ∃ S ∈ slPart H, ∃ c ∈ Subgroup.center H, A * A = S * c := by
  let c : H :=
    ⟨GeneralLinearGroup.scalar (Fin 2) (GeneralLinearGroup.det (A : GL (Fin 2) K)), hH A⟩
  have hc : c ∈ Subgroup.center H := by
    rw [Subgroup.mem_center_iff]
    intro B
    apply Subtype.ext
    show (B : GL (Fin 2) K) * ((c : H) : GL (Fin 2) K) =
      ((c : H) : GL (Fin 2) K) * (B : GL (Fin 2) K)
    exact (scalar_mul_comm (GeneralLinearGroup.det (A : GL (Fin 2) K)) (B : GL (Fin 2) K)).symm
  refine ⟨(A * A) * c⁻¹, ?_, c, hc, ?_⟩
  · rw [mem_slPart]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
    rw [show (c : GL (Fin 2) K) =
        GeneralLinearGroup.scalar (Fin 2) (GeneralLinearGroup.det (A : GL (Fin 2) K)) from rfl,
      GeneralLinearGroup.det_scalar, Fintype.card_fin]
    group
  · rw [mul_assoc, inv_mul_cancel, mul_one]

theorem sq_mem_slPart_sup_center
    (hH : ∀ A : H,
      GeneralLinearGroup.scalar (Fin 2) (GeneralLinearGroup.det (A : GL (Fin 2) K)) ∈ H)
    (A : H) :
    A * A ∈ slPart H ⊔ Subgroup.center H := by
  obtain ⟨S, hS, c, hc, hsq⟩ := exists_sq_eq_mul_mem_slPart_center hH A
  rw [hsq]
  exact Subgroup.mul_mem_sup hS hc

theorem gu2Stated_scalar_det_mem {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) (A : GU2Stated (p ^ f) K) :
    GeneralLinearGroup.scalar (Fin 2) (GeneralLinearGroup.det (A : GL (Fin 2) K)) ∈
      GU2Stated (p ^ f) K := by
  have hd : h.bar ((GeneralLinearGroup.det (A : GL (Fin 2) K) : Kˣ) : K) *
      ((GeneralLinearGroup.det (A : GL (Fin 2) K) : Kˣ) : K) = 1 := by
    rw [GeneralLinearGroup.val_det_apply]
    exact Lemma41aU3.bar_det_mul_det ((Lemma41aU3.mem_GU2Stated_iff h).mp A.2)
  rw [Lemma41aU3.mem_GU2Stated_iff h]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.mul_apply, Fin.sum_univ_two,
      hd, Matrix.diagonal_apply, ← GeneralLinearGroup.val_det_apply]

theorem gu2Stated_sq_mem_slPart_sup_center {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) (A : GU2Stated (p ^ f) K) :
    A * A ∈ slPart (GU2Stated (p ^ f) K) ⊔ Subgroup.center (GU2Stated (p ^ f) K) :=
  sq_mem_slPart_sup_center (fun B => gu2Stated_scalar_det_mem h B) A

end CFSG.LocalAnalysis.WeakClosure81

end
