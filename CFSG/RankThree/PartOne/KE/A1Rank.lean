module

public import CFSG.RankThree.SteinbergR3EEvenQuadraticSL2Fixed
public import CFSG.RankThree.Chevalley.SteinbergBIRootSL2Tools

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Classical (conjSL diagUnitOne coe_conjSL conjSL_mul coe_diagUnitOne)
open CFSG.RankThree.QuadraticSL2 (eq_scalar_of_commute commute_of_conjSL_eq)
open scoped Pointwise

variable {τ : Tag} {L : Type} [Field L]

theorem conj_rootSL2_torus_mul {θ : Fin τ.rank → ℤ} (hθ : IsRoot τ θ) (b : Fin τ.rank → Lˣ)
    (B A : SL2 L) :
    (rootDiagUnit τ b * rootSL2 τ L θ B) * rootSL2 τ L θ A *
        (rootDiagUnit τ b * rootSL2 τ L θ B)⁻¹ =
      rootSL2 τ L θ (conjSL (diagUnitOne (rootChar b θ) *
        Matrix.SpecialLinearGroup.toGL B) A) := by
  have hBA : rootSL2 τ L θ B * rootSL2 τ L θ A * (rootSL2 τ L θ B)⁻¹ =
      rootSL2 τ L θ (B * A * B⁻¹) := by
    rw [map_mul, map_mul, map_inv]
  have hconj : conjSL (Matrix.SpecialLinearGroup.toGL B) A = B * A * B⁻¹ := by
    apply Subtype.ext
    rw [coe_conjSL, ← map_inv, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul]
  rw [conjSL_mul, hconj, ← rootDiagUnit_conj_rootSL2 b hθ, ← hBA]
  group

theorem mem_torusGroup_of_centralizes_rootSL2 {θ : Fin τ.rank → ℤ} (hθ : IsRoot τ θ)
    {y : ModGL τ L}
    (hy : y ∈ (torusGroup τ L : Set (ModGL τ L)) * (rootRankOneGroup τ L θ : Set (ModGL τ L)))
    (hc : ∀ A : SL2 L, y * rootSL2 τ L θ A = rootSL2 τ L θ A * y) : y ∈ torusGroup τ L := by
  obtain ⟨t, ht, q, hq, rfl⟩ := hy
  obtain ⟨B, rfl⟩ := MonoidHom.mem_range.1 hq
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  have hinj : Function.Injective (rootSL2 τ L θ) := rootSL2_injective_of_field θ
  set X : GL (Fin 2) L := diagUnitOne (rootChar b θ) * Matrix.SpecialLinearGroup.toGL B with hX
  have hXA : ∀ A, conjSL X A = A := fun A => by
    apply hinj
    rw [← conj_rootSL2_torus_mul hθ b B A, hc A, mul_inv_cancel_right]
  have hXu := commute_of_conjSL_eq X (hXA (uSL 1))
  have hXv := commute_of_conjSL_eq X (hXA (vSL 1))
  have hscalar := eq_scalar_of_commute (X : Matrix (Fin 2) (Fin 2) L) hXu hXv
  have hXe : (X : Matrix (Fin 2) (Fin 2) L) = !![(rootChar b θ : L), 0; 0, 1] *
      (B : Matrix (Fin 2) (Fin 2) L) := by
    rw [hX, Units.val_mul, coe_diagUnitOne]
    rfl
  have h01 : (B : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 := by
    have h := congrFun (congrFun hscalar 0) 1
    rw [hXe] at h
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply] at h
    exact h
  have h10 : (B : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by
    have h := congrFun (congrFun hscalar 1) 0
    rw [hXe] at h
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply] using h
  have hdet : (B : Matrix (Fin 2) (Fin 2) L) 0 0 * (B : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 := by
    have := B.2
    rw [Matrix.det_fin_two, h01, h10] at this
    simpa using this
  set β : Lˣ := Units.mkOfMulEqOne _ _ hdet with hβ
  have hBH : B = HSL β := by
    ext i j
    fin_cases i <;> fin_cases j
    · rfl
    · simpa [coe_HSL] using h01
    · simpa [coe_HSL] using h10
    · have h11 : (B : Matrix (Fin 2) (Fin 2) L) 1 1 = ((β⁻¹ : Lˣ) : L) := by
        rw [hβ]
        simp only [Units.val_inv_eq_inv_val, Units.val_mkOfMulEqOne]
        exact (eq_inv_of_mul_eq_one_right hdet)
      simpa [coe_HSL] using h11
  rw [hBH]
  exact mul_mem ht ((exceptional_Lang_root_rank_one_torus_transport τ L hθ).2.1 β)

end CFSG.RankThree.PartOne.KE
