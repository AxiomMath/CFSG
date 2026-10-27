module

public import CFSG.LieType.Universal.Unitary.Basic

public section

namespace CFSG.RankThree.PartOne.KFK0

open Matrix CFSG.LieType.Universal.Unitary

variable {K : Type} [Field K]

@[expose] def hf (σ : K ≃+* K) (v w : Fin 3 → K) : K :=
  σ (v 0) * w 2 + σ (v 1) * w 1 + σ (v 2) * w 0

variable {σ : K ≃+* K}

theorem hf_add_right (v w w' : Fin 3 → K) : hf σ v (w + w') = hf σ v w + hf σ v w' := by
  simp only [hf, Pi.add_apply]
  ring

theorem hf_smul_left (c : K) (v w : Fin 3 → K) : hf σ (c • v) w = σ c * hf σ v w := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, map_mul]
  ring

theorem hf_smul_right (c : K) (v w : Fin 3 → K) : hf σ v (c • w) = c * hf σ v w := by
  simp only [hf, Pi.smul_apply, smul_eq_mul]
  ring

theorem hf_zero_right (v : Fin 3 → K) : hf σ v 0 = 0 := by simp [hf]

theorem hf_comm (hσ : ∀ c, σ (σ c) = c) (v w : Fin 3 → K) : hf σ w v = σ (hf σ v w) := by
  simp only [hf, map_add, map_mul, hσ]
  ring

theorem hf_eq_dotProduct (σ : K ≃+* K) (v w : Fin 3 → K) :
    hf σ v w = (fun i => σ (v i)) ⬝ᵥ (antidiag 3 : Matrix (Fin 3) (Fin 3) K) *ᵥ w := by
  simp [hf, dotProduct, Matrix.mulVec, Fin.sum_univ_three, antidiag, Fin.rev]

@[expose] def smat (g : ↥(SU σ 3)) : Matrix (Fin 3) (Fin 3) K := ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)

theorem smat_mul (g h : ↥(SU σ 3)) : smat (g * h) = smat g * smat h := rfl

theorem smat_one : smat (1 : ↥(SU σ 3)) = 1 := rfl

theorem smat_inv_mul (g : ↥(SU σ 3)) : smat g⁻¹ * smat g = 1 := by
  rw [← smat_mul, inv_mul_cancel, smat_one]

theorem smat_mul_inv (g : ↥(SU σ 3)) : smat g * smat g⁻¹ = 1 := by
  rw [← smat_mul, mul_inv_cancel, smat_one]

theorem smat_gram (g : ↥(SU σ 3)) :
    conjTr σ (smat g) * antidiag 3 * smat g = antidiag 3 := g.2.2

theorem mulVec_dotProduct_eq (A : Matrix (Fin 3) (Fin 3) K) (a b : Fin 3 → K) :
    (A *ᵥ a) ⬝ᵥ b = a ⬝ᵥ (Aᵀ *ᵥ b) := by
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_three, Matrix.transpose_apply]
  ring

theorem hf_mulVec_SU (g : ↥(SU σ 3)) (v w : Fin 3 → K) :
    hf σ (smat g *ᵥ v) (smat g *ᵥ w) = hf σ v w := by
  rw [hf_eq_dotProduct, hf_eq_dotProduct]
  have h1 : (fun i => σ ((smat g *ᵥ v) i)) = ((smat g).map σ) *ᵥ (fun i => σ (v i)) := by
    ext i
    exact RingHom.map_mulVec σ.toRingHom _ _ i
  rw [h1, mulVec_dotProduct_eq, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have h2 : ((smat g).map σ)ᵀ = conjTr σ (smat g) := rfl
  rw [h2, smat_gram]

theorem eq_zero_of_hf_right (hσ : Function.Injective σ) {v : Fin 3 → K} (h : ∀ w, hf σ v w = 0) :
    v = 0 := by
  have h0 := h ![1, 0, 0]
  have h1 := h ![0, 1, 0]
  have h2 := h ![0, 0, 1]
  simp [hf] at h0 h1 h2
  ext i
  fin_cases i
  · simpa using hσ (by rw [h2, map_zero])
  · simpa using hσ (by rw [h1, map_zero])
  · simpa using hσ (by rw [h0, map_zero])

end CFSG.RankThree.PartOne.KFK0
