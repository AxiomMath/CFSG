module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonClassification
import Mathlib.LinearAlgebra.Matrix.Trace

namespace CFSG
end CFSG
open CFSG

/-!
# Trace fields in Dickson's subfield alternatives

The simultaneous projective conjugacy retained by
`Dickson.SubfieldConjugacyWitness` forces the normalized trace of any ordered
pair of determinant-one lifts to lie in the witnessed subfield.
-/

noncomputable section

open BenderSuzuki.MatrixGroups

namespace CFSG.Glauberman.Dickson

open scoped MatrixGroups

universe u

/-- If two elements of a subgroup of `PSL₂(F)` are simultaneously
projectively conjugate to matrices over the Dickson subfield, then the
scaling-independent ratio `tr(AB) / (tr(A) tr(B))` belongs to that subfield. -/
public theorem normalizedTrace_mem_subfield
    {F : Type u} [Field F] [Finite F]
    (H : Subgroup (PSL2MatrixGroup F)) {p m : ℕ}
    (W : SubfieldConjugacyWitness p m H)
    (a b : H) (A B : Matrix.SpecialLinearGroup (Fin 2) F)
    (ha : (a : PSL2MatrixGroup F) =
      QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) A)
    (hb : (b : PSL2MatrixGroup F) =
      QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) B)
    (htrA : Matrix.trace (A : Matrix (Fin 2) (Fin 2) F) ≠ 0)
    (htrB : Matrix.trace (B : Matrix (Fin 2) (Fin 2) F) ≠ 0) :
    Matrix.trace ((A * B : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) /
      (Matrix.trace (A : Matrix (Fin 2) (Fin 2) F) *
        Matrix.trace (B : Matrix (Fin 2) (Fin 2) F)) ∈ W.K := by
  rcases Matrix.ProjGenLinGroup.mk_surjective (W.phi a) with ⟨A0, hA0⟩
  rcases Matrix.ProjGenLinGroup.mk_surjective (W.phi b) with ⟨B0, hB0⟩
  rcases Matrix.ProjGenLinGroup.mk_surjective W.conjugator with ⟨C, hC⟩
  have hAproj :
      Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map W.K.subtype A0) =
        Matrix.ProjGenLinGroup.mk
          (C * Matrix.SpecialLinearGroup.toGL A * C⁻¹) := by
    calc
      Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map W.K.subtype A0) =
          h826_pglMap W.K.subtype (W.phi a) := by
            rw [← hA0, h826_pglMap_mk]
      _ = W.conjugator * h826_pslToPGL (a : PSL2MatrixGroup F) *
          W.conjugator⁻¹ := W.map_phi a
      _ = Matrix.ProjGenLinGroup.mk
          (C * Matrix.SpecialLinearGroup.toGL A * C⁻¹) := by
            rw [ha, h826_pslToPGL_mk, ← hC]
            simp only [map_mul, map_inv]
  have hBproj :
      Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map W.K.subtype B0) =
        Matrix.ProjGenLinGroup.mk
          (C * Matrix.SpecialLinearGroup.toGL B * C⁻¹) := by
    calc
      Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map W.K.subtype B0) =
          h826_pglMap W.K.subtype (W.phi b) := by
            rw [← hB0, h826_pglMap_mk]
      _ = W.conjugator * h826_pslToPGL (b : PSL2MatrixGroup F) *
          W.conjugator⁻¹ := W.map_phi b
      _ = Matrix.ProjGenLinGroup.mk
          (C * Matrix.SpecialLinearGroup.toGL B * C⁻¹) := by
            rw [hb, h826_pslToPGL_mk, ← hC]
            simp only [map_mul, map_inv]
  rcases Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hAproj with ⟨u, hu⟩
  rcases Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hBproj with ⟨v, hv⟩
  let tA0 : W.K := Matrix.trace (A0 : Matrix (Fin 2) (Fin 2) W.K)
  let tB0 : W.K := Matrix.trace (B0 : Matrix (Fin 2) (Fin 2) W.K)
  let tAB0 : W.K := Matrix.trace
    ((A0 * B0 : GL (Fin 2) W.K) : Matrix (Fin 2) (Fin 2) W.K)
  have htraceA :
      Matrix.trace (A : Matrix (Fin 2) (Fin 2) F) =
        W.K.subtype tA0 * (u : F) := by
    have h := congrArg
      (fun X : GL (Fin 2) F => Matrix.trace (X : Matrix (Fin 2) (Fin 2) F)) hu
    simp only [Matrix.GeneralLinearGroup.coe_mul] at h
    rw [Matrix.trace_units_conj] at h
    have htoGLA :
        ((Matrix.SpecialLinearGroup.toGL A : GL (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) =
        (A : Matrix (Fin 2) (Fin 2) F) := rfl
    rw [htoGLA] at h
    rw [← h]
    simp [tA0, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.GeneralLinearGroup.coe_scalar]
    ring
  have htraceB :
      Matrix.trace (B : Matrix (Fin 2) (Fin 2) F) =
        W.K.subtype tB0 * (v : F) := by
    have h := congrArg
      (fun X : GL (Fin 2) F => Matrix.trace (X : Matrix (Fin 2) (Fin 2) F)) hv
    simp only [Matrix.GeneralLinearGroup.coe_mul] at h
    rw [Matrix.trace_units_conj] at h
    have htoGLB :
        ((Matrix.SpecialLinearGroup.toGL B : GL (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) =
        (B : Matrix (Fin 2) (Fin 2) F) := rfl
    rw [htoGLB] at h
    rw [← h]
    simp [tB0, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.GeneralLinearGroup.coe_scalar]
    ring
  have hAB :
      Matrix.GeneralLinearGroup.map W.K.subtype (A0 * B0) *
          Matrix.GeneralLinearGroup.scalar (Fin 2) (u * v) =
        C * Matrix.SpecialLinearGroup.toGL (A * B) * C⁻¹ := by
    calc
      Matrix.GeneralLinearGroup.map W.K.subtype (A0 * B0) *
          Matrix.GeneralLinearGroup.scalar (Fin 2) (u * v) =
          (Matrix.GeneralLinearGroup.map W.K.subtype A0 *
              Matrix.GeneralLinearGroup.scalar (Fin 2) u) *
            (Matrix.GeneralLinearGroup.map W.K.subtype B0 *
              Matrix.GeneralLinearGroup.scalar (Fin 2) v) := by
                apply Matrix.GeneralLinearGroup.ext
                intro i j
                fin_cases i <;> fin_cases j <;>
                  simp [Matrix.mul_apply, Fin.sum_univ_two,
                    Matrix.GeneralLinearGroup.coe_scalar] <;> ring
      _ = (C * Matrix.SpecialLinearGroup.toGL A * C⁻¹) *
          (C * Matrix.SpecialLinearGroup.toGL B * C⁻¹) := by rw [hu, hv]
      _ = C * Matrix.SpecialLinearGroup.toGL (A * B) * C⁻¹ := by
        rw [map_mul]
        group
  have htraceAB :
      Matrix.trace ((A * B : Matrix.SpecialLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) =
        W.K.subtype tAB0 * ((u * v : Fˣ) : F) := by
    have h := congrArg
      (fun X : GL (Fin 2) F => Matrix.trace (X : Matrix (Fin 2) (Fin 2) F)) hAB
    simp only [Matrix.GeneralLinearGroup.coe_mul] at h
    rw [Matrix.trace_units_conj] at h
    have htoGLAB :
        ((Matrix.SpecialLinearGroup.toGL (A * B) : GL (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) =
        ((A * B : Matrix.SpecialLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) := rfl
    rw [htoGLAB] at h
    rw [← h]
    simp [tAB0, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.GeneralLinearGroup.coe_scalar]
    ring
  have htA0 : tA0 ≠ 0 := by
    intro ht
    apply htrA
    rw [htraceA, ht]
    simp
  have htB0 : tB0 ≠ 0 := by
    intro ht
    apply htrB
    rw [htraceB, ht]
    simp
  have htA0F : W.K.subtype tA0 ≠ 0 := by
    intro h
    apply htA0
    apply Subtype.ext
    exact h
  have htB0F : W.K.subtype tB0 ≠ 0 := by
    intro h
    apply htB0
    apply Subtype.ext
    exact h
  let z : W.K := tAB0 / (tA0 * tB0)
  have hz : Matrix.trace ((A * B : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) /
      (Matrix.trace (A : Matrix (Fin 2) (Fin 2) F) *
        Matrix.trace (B : Matrix (Fin 2) (Fin 2) F)) =
    W.K.subtype z := by
    rw [htraceA, htraceB, htraceAB]
    change W.K.subtype tAB0 * ((u * v : Fˣ) : F) /
        ((W.K.subtype tA0 * (u : F)) *
          (W.K.subtype tB0 * (v : F))) =
      W.K.subtype tAB0 / (W.K.subtype tA0 * W.K.subtype tB0)
    field_simp [htA0F, htB0F]
    simp only [Units.val_mul]
    ring
  rw [hz]
  exact z.property

end CFSG.Glauberman.Dickson
