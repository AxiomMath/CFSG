module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45FinalTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
public import CFSG.LinearAlgebra.SteinbergBQEvenSL2OddCyclic

public section

namespace CFSG.StandardType

namespace RawTorusPClassical

open CFSG CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

section Recipe

variable {K : Type} [Field K] [CharP K 2]

variable [Finite K]

theorem exists_conj_eq_of_mem_two {φ : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin 2) K))}
    (hφ : φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 2) K)) Set.univ) :
    ∃ r, φ = MulAut.conj r := by
  classical
  have := Fintype.ofFinite K
  obtain ⟨A, -, hA⟩ := hφ
  have hchar : ringChar K = 2 := ringChar.eq K 2
  obtain ⟨l, hl⟩ := FiniteField.isSquare_of_char_two hchar
    ((Matrix.GeneralLinearGroup.det A : Kˣ) : K)
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hl
    exact (Matrix.GeneralLinearGroup.det A).ne_zero hl
  set c : Kˣ := (Units.mk0 l hl0)⁻¹ with hc
  set B : GL (Fin 2) K := Matrix.GeneralLinearGroup.scalar (Fin 2) c * A with hB
  have hBdet : B ∈ LargeEvenSLGroup (Fin 2) K := by
    rw [TypeA.mem_largeEvenSLGroup_iff, hB, Units.val_mul, Matrix.det_mul,
      Matrix.GeneralLinearGroup.coe_scalar, scalar_apply, det_diagonal, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, ← Matrix.GeneralLinearGroup.val_det_apply, hl, hc,
      Units.val_inv_eq_inv_val, Units.val_mk0]
    field_simp
  refine ⟨LargeEvenProjMk (LargeEvenSLGroup (Fin 2) K) ⟨B, hBdet⟩, ?_⟩
  ext x
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective _ x
  have hmem : A * (h : GL (Fin 2) K) * A⁻¹ ∈ LargeEvenSLGroup (Fin 2) K := by
    have h2 : Matrix.GeneralLinearGroup.det (h : GL (Fin 2) K) = 1 := h.2
    change Matrix.GeneralLinearGroup.det (A * (h : GL (Fin 2) K) * A⁻¹) = 1
    rw [map_mul, map_mul, map_inv, h2, mul_one, mul_inv_cancel]
  rw [hA h ⟨_, hmem⟩ rfl, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  change A * (h : GL (Fin 2) K) * A⁻¹ = B * (h : GL (Fin 2) K) * B⁻¹
  have hcomm := TypeA.commute_scalar_GL c (A * (h : GL (Fin 2) K) * A⁻¹)
  calc A * (h : GL (Fin 2) K) * A⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 2) c * (A * (h : GL (Fin 2) K) * A⁻¹) *
        (Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ := by rw [hcomm.eq, mul_inv_cancel_right]
    _ = B * (h : GL (Fin 2) K) * B⁻¹ := by rw [hB]; group

end Recipe

end RawTorusPClassical

open CFSG.Assembly RawTorusPClassical

end CFSG.StandardType

end
