module

public import CFSG.Quasithin.EmptyFaithful.A38c17Defs
public import CFSG.LieType.Steinberg.CentralExt.SUTwo

public section

namespace CFSG.Quasithin.A38c17

open Matrix CFSG.LieType.Steinberg CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Finite K] [CharP K p]

theorem conjTr_hypMat_mul_antidiag_mul_hypMat {ζ : K} (hζ0 : ζ ≠ 0)
    (hζ : unitaryInvolution K p 1 ζ = -ζ) (B : Matrix (Fin 2) (Fin 2) (fixedSubfield K p 1)) :
    conjTr (unitaryInvolution K p 1) (hypMat ζ B) * antidiag 2 * hypMat ζ B =
      ((B.det : fixedSubfield K p 1) : K) • antidiag 2 := by
  rw [conjTr_hypMat hζ B, antidiag_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hypMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] <;> field_simp <;> ring

@[expose] noncomputable def hypMonoidHom {ζ : K} (hζ0 : ζ ≠ 0) :
    Matrix (Fin 2) (Fin 2) (fixedSubfield K p 1) →* Matrix (Fin 2) (Fin 2) K where
  toFun := hypMat ζ
  map_one' := hypMat_one
  map_mul' := hypMat_mul hζ0

@[expose] noncomputable def hypEmbedGL {ζ : K} (hζ0 : ζ ≠ 0) :
    GL (Fin 2) (fixedSubfield K p 1) →* GL (Fin 2) K :=
  Units.map (hypMonoidHom hζ0)

theorem coe_hypEmbedGL {ζ : K} (hζ0 : ζ ≠ 0) (B : GL (Fin 2) (fixedSubfield K p 1)) :
    ((hypEmbedGL hζ0 B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      hypMat ζ (B : Matrix (Fin 2) (Fin 2) (fixedSubfield K p 1)) := rfl

theorem scalar_mul_hypEmbedGL_mem_GU {ζ : K} (hζ0 : ζ ≠ 0) (hζ : unitaryInvolution K p 1 ζ = -ζ)
    (B : GL (Fin 2) (fixedSubfield K p 1)) (μ : Kˣ)
    (hμ : unitaryInvolution K p 1 μ * μ *
      (((B : Matrix (Fin 2) (Fin 2) (fixedSubfield K p 1)).det : fixedSubfield K p 1) : K) = 1) :
    GeneralLinearGroup.scalar (Fin 2) μ * hypEmbedGL hζ0 B ∈ GU (unitaryInvolution K p 1) 2 := by
  rw [mem_GU, Units.val_mul, coe_hypEmbedGL, GeneralLinearGroup.coe_scalar]
  have hs : ∀ X : Matrix (Fin 2) (Fin 2) K, Matrix.scalar (Fin 2) (μ : K) * X = (μ : K) • X := by
    intro X
    rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
  have hc : ∀ X : Matrix (Fin 2) (Fin 2) K,
      conjTr (unitaryInvolution K p 1) ((μ : K) • X) =
        unitaryInvolution K p 1 (μ : K) • conjTr (unitaryInvolution K p 1) X := by
    intro X
    ext i j
    simp [conjTr]
  rw [hs, hc]
  simp only [Matrix.smul_mul, Matrix.mul_smul]
  rw [conjTr_hypMat_mul_antidiag_mul_hypMat hζ0 hζ, smul_smul, smul_smul, mul_comm (μ : K), hμ,
    one_smul]

end CFSG.Quasithin.A38c17
