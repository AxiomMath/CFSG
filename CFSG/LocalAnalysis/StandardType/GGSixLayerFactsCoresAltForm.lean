module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCoresSkolem
public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryHermitian
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

public section

namespace CFSG.StandardType

namespace LayerCores

open Matrix CFSG.LocalAnalysis.ComponentInitial

variable {D : Type} [Field D] {d : ℕ} {T : Matrix (Fin d) (Fin d) D → Matrix (Fin d) (Fin d) D}

theorem IsInvol.exists_gram_id (hT : IsInvol T)
    (h1 : ∀ c, T (Matrix.scalar (Fin d) c) = Matrix.scalar (Fin d) c) :
    ∃ H : GL (Fin d) D, ∀ x, T x =
      ((H⁻¹ : GL (Fin d) D) : Matrix (Fin d) (Fin d) D) * xᵀ * (H : Matrix (Fin d) (Fin d) D) := by
  obtain ⟨H, hH⟩ := hT.exists_gram (RingHom.id D) h1 fun _ => rfl
  refine ⟨H, fun x => ?_⟩
  rw [hH]
  congr 2

section Gram

variable (hT : IsInvol T) (H : GL (Fin d) D)
  (hH : ∀ x, T x = ((H⁻¹ : GL (Fin d) D) : Matrix (Fin d) (Fin d) D) * xᵀ *
    (H : Matrix (Fin d) (Fin d) D))
include hT hH

theorem transpose_gram_eq [CharP D 2] [NeZero d] :
    (H : Matrix (Fin d) (Fin d) D)ᵀ = H := by
  set M : Matrix (Fin d) (Fin d) D := ↑H with hM
  set Mi : Matrix (Fin d) (Fin d) D := ((H⁻¹ : GL (Fin d) D) : Matrix (Fin d) (Fin d) D)
  have hMMi : M * Mi = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hMiM : Mi * M = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hZ : ∀ x : Matrix (Fin d) (Fin d) D, x * (Mi * Mᵀ) = (Mi * Mᵀ) * x := by
    intro x
    have h1 : x = Mi * Mᵀ * x * (Miᵀ * M) := by
      have h0 := hT.invol x
      rw [hH, hH, transpose_mul, transpose_mul, transpose_transpose] at h0
      calc x = Mi * (Mᵀ * (x * Miᵀ)) * M := h0.symm
        _ = _ := by simp only [Matrix.mul_assoc]
    have h2 : Miᵀ * M * (Mi * Mᵀ) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc M, hMMi, Matrix.one_mul, ← transpose_mul, hMMi,
        transpose_one]
    calc x * (Mi * Mᵀ) = Mi * Mᵀ * x * (Miᵀ * M * (Mi * Mᵀ)) := by
          conv_lhs => rw [h1]
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h2, Matrix.mul_one]
  have hc : Mi * Mᵀ ∈ Set.center (Matrix (Fin d) (Fin d) D) := by
    rw [Semigroup.mem_center_iff]
    exact hZ
  rw [Matrix.center_eq_range] at hc
  obtain ⟨c, hc⟩ := hc
  have hMt : Mᵀ = c • M := by
    calc Mᵀ = M * (Mi * Mᵀ) := by rw [← Matrix.mul_assoc, hMMi, Matrix.one_mul]
      _ = c • M := by rw [← hc, Matrix.scalar_apply, ← smul_eq_mul_diagonal]
  have hcc : (c * c) • M = M := by
    calc (c * c) • M = c • Mᵀ := by rw [hMt, smul_smul]
      _ = (c • M)ᵀ := by rw [transpose_smul]
      _ = M := by rw [← hMt, transpose_transpose]
  have hcc' : c * c = 1 := by
    have h3 : (c * c) • (1 : Matrix (Fin d) (Fin d) D) = 1 := by
      calc (c * c) • (1 : Matrix (Fin d) (Fin d) D) = ((c * c) • M) * Mi := by
            rw [Matrix.smul_mul, hMMi]
        _ = 1 := by rw [hcc, hMMi]
    have h4 := congrFun (congrFun h3 0) 0
    simpa using h4
  have hc1 : c = 1 := by
    have h5 : (c + 1) * (c + 1) = 0 := by
      rw [add_mul, mul_add, mul_add, hcc', mul_one, one_mul, mul_one, add_assoc,
        ← add_assoc c c, CharTwo.add_self_eq_zero, zero_add, CharTwo.add_self_eq_zero]
    have h6 : c + 1 = 0 := mul_self_eq_zero.mp h5
    rw [← CharTwo.neg_eq (1 : D)]
    exact eq_neg_of_add_eq_zero_left h6
  rw [hMt, hc1, one_smul]

omit hT in
theorem gram_eq_add_transpose (hsym : (H : Matrix (Fin d) (Fin d) D)ᵀ = H)
    {y : Matrix (Fin d) (Fin d) D} (hy : y + T y = 1) :
    (H : Matrix (Fin d) (Fin d) D) = (H : Matrix (Fin d) (Fin d) D) * y +
      ((H : Matrix (Fin d) (Fin d) D) * y)ᵀ := by
  have hMMi : (H : Matrix (Fin d) (Fin d) D) * ((H⁻¹ : GL (Fin d) D) :
      Matrix (Fin d) (Fin d) D) = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  calc (H : Matrix (Fin d) (Fin d) D) = H * (y + T y) := by rw [hy, Matrix.mul_one]
    _ = H * y + yᵀ * H := by
      rw [Matrix.mul_add, hH, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hMMi, Matrix.one_mul]
    _ = _ := by rw [transpose_mul, hsym]

end Gram


section Form

theorem isAlt_toBilin'_add_transpose [CharP D 2] (N : Matrix (Fin d) (Fin d) D) :
    (Matrix.toBilin' (N + Nᵀ)).IsAlt := by
  intro v
  rw [Matrix.toBilin'_apply', Matrix.add_mulVec, dotProduct_add, Matrix.mulVec_transpose,
    dotProduct_comm v (v ᵥ* N), ← Matrix.dotProduct_mulVec, CharTwo.add_self_eq_zero]

theorem nondegenerate_toBilin'_gram (H : GL (Fin d) D) :
    (Matrix.toBilin' (H : Matrix (Fin d) (Fin d) D)).Nondegenerate :=
  LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mp H.isUnit).ne_zero

theorem toLin_mem_sesqUnitaryGroup_iff (M : Matrix (Fin d) (Fin d) D) (g : GL (Fin d) D) :
    Matrix.GeneralLinearGroup.toLin g ∈ sesqUnitaryGroup (Matrix.toBilin' M) ↔
      (g : Matrix (Fin d) (Fin d) D)ᵀ * M * g = M := by
  rw [mem_sesqUnitaryGroup, Matrix.GeneralLinearGroup.coe_toLin]
  constructor
  · intro h
    apply Matrix.toBilin'.injective
    rw [← Matrix.toBilin'_comp]
    refine LinearMap.ext₂ fun x y => ?_
    exact h x y
  · intro h x y
    have h1 := congrArg (fun N => Matrix.toBilin' N x y) h
    simp only [← Matrix.toBilin'_comp] at h1
    exact h1

variable (hT : IsInvol T) (H : GL (Fin d) D)
  (hH : ∀ x, T x = ((H⁻¹ : GL (Fin d) D) : Matrix (Fin d) (Fin d) D) * xᵀ *
    (H : Matrix (Fin d) (Fin d) D))
include hH

omit hT in
theorem mem_matUnitary_iff_gram {hT : IsInvol T} {g : GL (Fin d) D} :
    g ∈ matUnitary hT ↔ (g : Matrix (Fin d) (Fin d) D)ᵀ * H * g = H := by
  have hMMi : (H : Matrix (Fin d) (Fin d) D) * ((H⁻¹ : GL (Fin d) D) :
      Matrix (Fin d) (Fin d) D) = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hMiM : ((H⁻¹ : GL (Fin d) D) : Matrix (Fin d) (Fin d) D) *
      (H : Matrix (Fin d) (Fin d) D) = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [mem_matUnitary, hH]
  constructor
  · intro h
    calc (g : Matrix (Fin d) (Fin d) D)ᵀ * H * g
        = H * (((H⁻¹ : GL (Fin d) D) : Matrix (Fin d) (Fin d) D) *
          (g : Matrix (Fin d) (Fin d) D)ᵀ * H * g) := by
          simp only [← Matrix.mul_assoc, hMMi, Matrix.one_mul]
      _ = H := by rw [h, Matrix.mul_one]
  · intro h
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ _ (g : Matrix (Fin d) (Fin d) D),
      h, hMiM]

omit hT in
theorem map_toLin_matUnitary {hT : IsInvol T} :
    (matUnitary hT).map (Matrix.GeneralLinearGroup.toLin : GL (Fin d) D ≃*
      LinearMap.GeneralLinearGroup D (Fin d → D)).toMonoidHom =
      sesqUnitaryGroup (Matrix.toBilin' (H : Matrix (Fin d) (Fin d) D)) := by
  ext g'
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (toLin_mem_sesqUnitaryGroup_iff _ g).mpr ((mem_matUnitary_iff_gram H hH).mp hg)
  · intro hg'
    refine ⟨Matrix.GeneralLinearGroup.toLin.symm g', (mem_matUnitary_iff_gram H hH).mpr ?_, ?_⟩
    · rw [← toLin_mem_sesqUnitaryGroup_iff, MulEquiv.apply_symm_apply]
      exact hg'
    · exact MulEquiv.apply_symm_apply _ _

end Form

end LayerCores

end CFSG.StandardType
