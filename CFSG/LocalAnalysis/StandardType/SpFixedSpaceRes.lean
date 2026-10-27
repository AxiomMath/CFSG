module

public import CFSG.LocalAnalysis.StandardType.SpFixedSpaceDual

public section

namespace CFSG.StandardType

namespace SpFixed

open Matrix
open CFSG.Open (StatedSp)

variable {F : Type} [Field F] {n m : ℕ} {N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}
  {B : Matrix (Fin n ⊕ Fin n) (Fin m ⊕ Fin m) F}

theorem IsFixedBasis.dualMat_mul_mul_mul (h : IsFixedBasis N B)
    (g g' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (hg' : N * g' = g' * N) :
    dualMat B * (g * g') * B = (dualMat B * g * B) * (dualMat B * g' * B) := by
  calc dualMat B * (g * g') * B
      = dualMat B * g * g' * B := by simp only [Matrix.mul_assoc]
    _ = dualMat B * g * g' * (N * B) := by rw [h.fixed]
    _ = dualMat B * g * g' * N * B := by simp only [Matrix.mul_assoc]
    _ = dualMat B * g * (g' * N) * B := by simp only [Matrix.mul_assoc]
    _ = dualMat B * g * (N * g') * B := by rw [hg']
    _ = dualMat B * g * N * g' * B := by simp only [Matrix.mul_assoc]
    _ = dualMat B * g * (B * dualMat B) * g' * B := by rw [h.self_mul_dualMat]
    _ = (dualMat B * g * B) * (dualMat B * g' * B) := by simp only [Matrix.mul_assoc]

theorem IsFixedBasis.res_transpose_mul_gram_mul (h : IsFixedBasis N B)
    {g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F} (hg : N * g = g * N)
    (hs : gᵀ * gram F n * g = gram F n) :
    (dualMat B * g * B)ᵀ * gram F m * (dualMat B * g * B) = gram F m := by
  calc (dualMat B * g * B)ᵀ * gram F m * (dualMat B * g * B)
      = Bᵀ * gᵀ * ((dualMat B)ᵀ * gram F m * dualMat B) * g * B := by
        rw [Matrix.transpose_mul, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
    _ = Bᵀ * gᵀ * (gram F n * N) * g * B := by rw [h.dualMat_transpose_mul_gram_mul]
    _ = Bᵀ * gᵀ * gram F n * (N * g) * B := by simp only [Matrix.mul_assoc]
    _ = Bᵀ * gᵀ * gram F n * (g * N) * B := by rw [hg]
    _ = Bᵀ * (gᵀ * gram F n * g) * (N * B) := by simp only [Matrix.mul_assoc]
    _ = Bᵀ * (gᵀ * gram F n * g) * B := by rw [h.fixed]
    _ = Bᵀ * gram F n * B := by rw [hs]
    _ = gram F m := h.form

theorem IsFixedBasis.exists_res (h : IsFixedBasis N B) (C : Subgroup (StatedSp n F))
    (hC : ∀ g ∈ C, N * matHom F n g = matHom F n g * N) :
    ∃ res : C →* StatedSp m F,
      ∀ g : C, matHom F m (res g) = dualMat B * matHom F n (g : StatedSp n F) * B := by
  let r : C → Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F :=
    fun g => dualMat B * matHom F n (g : StatedSp n F) * B
  have hr_mul : ∀ g g' : C, r (g * g') = r g * r g' := by
    intro g g'
    change dualMat B * matHom F n ((g * g' : C) : StatedSp n F) * B =
      (dualMat B * matHom F n (g : StatedSp n F) * B) *
        (dualMat B * matHom F n (g' : StatedSp n F) * B)
    rw [Subgroup.coe_mul, map_mul]
    exact h.dualMat_mul_mul_mul (matHom F n (g : StatedSp n F)) (matHom F n (g' : StatedSp n F))
      (hC (g' : StatedSp n F) g'.2)
  have hr_one : r 1 = 1 := by
    change dualMat B * matHom F n ((1 : C) : StatedSp n F) * B = 1
    rw [Subgroup.coe_one, map_one, Matrix.mul_one]
    exact dualMat_mul_self h.form
  let resFun : C → StatedSp m F := fun g =>
    ⟨Units.mk (r g) (r g⁻¹)
        (by rw [← hr_mul g g⁻¹, mul_inv_cancel, hr_one])
        (by rw [← hr_mul g⁻¹ g, inv_mul_cancel, hr_one]),
      CFSG.Open.StatedAPI.mem_statedSp_iff.2 (by
        change (dualMat B * matHom F n (g : StatedSp n F) * B)ᵀ * gram F m *
          (dualMat B * matHom F n (g : StatedSp n F) * B) = gram F m
        exact h.res_transpose_mul_gram_mul (hC (g : StatedSp n F) g.2)
          (matHom_transpose_mul_gram_mul (g : StatedSp n F)))⟩
  refine ⟨{ toFun := resFun
            map_one' := ?_
            map_mul' := ?_ }, ?_⟩
  · apply Subtype.ext
    apply Units.ext
    show r (1 : C) = 1
    exact hr_one
  · intro g g'
    apply Subtype.ext
    apply Units.ext
    show r (g * g') = r g * r g'
    exact hr_mul g g'
  · intro g
    rfl

end SpFixed

end CFSG.StandardType
