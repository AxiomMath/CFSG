module

public import CFSG.GF2Type.Widths1112.Co2Module.Inputs

public section

open CFSG.GF2Type.Widths1112.Co2Module CFSG.GF2W1112
open scoped Matrix

namespace CertificateChecks.Batch38956

open CFSG.GF2Type.Widths1112.Co2Module CFSG.GF2W1112
open scoped Matrix

private theorem uA_mul_uAInv : ∀ k ∈ w12UNormIdx, uA k * uAInv k = 1 := by decide +kernel

private theorem card_cls_zero : (lineReps.filter fun w => uCls w = 0).card = 30 := by
  decide +kernel

private theorem card_cls_one : (lineReps.filter fun w => uCls w = 1).card = 10 := by
  decide +kernel

private theorem tree_spec : ∀ w ∈ lineReps, w ≠ uRoot (uCls w) →
    uPar w ∈ lineReps ∧ uCls (uPar w) = uCls w ∧ uDepth (uPar w) < uDepth w ∧ uC w ≠ 0 ∧
      Matrix.vecMul w (uA (4 + (uGen w).val)) = uC w • uPar w := by decide +kernel

private theorem uW1_spec : uW1 ∈ lineReps ∧ uCls uW1 = 1 ∧ uW1 ⬝ᵥ uV0 ≠ 0 := by decide +kernel

private theorem uW_spec :
    Function.Injective uW ∧ (∀ i, uW i ∈ lineReps) ∧ (∀ i, uCls (uW i) = 1) := by decide +kernel

private theorem uCr_spec :
    ∀ i : Fin 10, uCr i ≠ 0 ∧ Matrix.vecMul (uW i) (uA (6 + i.val)) = uCr i • uW1 := by
  decide +kernel

private theorem uCt_spec : uCt ≠ 0 ∧ Matrix.vecMul uW1 (uA 16) = uCt • uW1 := by decide +kernel

private theorem uP_fix : ∀ j : Fin 5, Matrix.vecMul uW1 (uA (17 + j.val)) = uW1 := by
  decide +kernel

private theorem ord_p : ∀ j : Fin 5, ∃ k : ℕ, w12UOrd (17 + j.val) = 2 ^ k := by
  intro j
  fin_cases j
  · exact ⟨2, by decide⟩
  · exact ⟨2, by decide⟩
  · exact ⟨1, by decide⟩
  · exact ⟨2, by decide⟩
  · exact ⟨2, by decide⟩

private theorem ord_pos : ∀ i : Fin 33, 0 < w12UOrd i.val := by decide +kernel

private theorem uVec_conjCode :
    ∀ k ∈ w12UNormIdx, ∀ i : Fin 4, uVec (w12UConjCode k i.val) = fun r => uA k r i := by
  decide +kernel

end CertificateChecks.Batch38956

namespace Certificates

open CertificateChecks

open CFSG.GF2Type.Widths1112.Co2Module CFSG.GF2W1112 in
open scoped Matrix in
theorem certificate38956 :
    (∀ k ∈ w12UNormIdx, uA k * uAInv k = 1)
    ∧ ((lineReps.filter fun w => uCls w = 0).card = 30)
    ∧ ((lineReps.filter fun w => uCls w = 1).card = 10)
    ∧ (∀ w ∈ lineReps, w ≠ uRoot (uCls w) →
      uPar w ∈ lineReps ∧ uCls (uPar w) = uCls w ∧ uDepth (uPar w) < uDepth w ∧ uC w ≠ 0 ∧
        Matrix.vecMul w (uA (4 + (uGen w).val)) = uC w • uPar w)
    ∧ (uW1 ∈ lineReps ∧ uCls uW1 = 1 ∧ uW1 ⬝ᵥ uV0 ≠ 0)
    ∧ (Function.Injective uW ∧ (∀ i, uW i ∈ lineReps) ∧ (∀ i, uCls (uW i) = 1))
    ∧ (∀ i : Fin 10, uCr i ≠ 0 ∧ Matrix.vecMul (uW i) (uA (6 + i.val)) = uCr i • uW1)
    ∧ (uCt ≠ 0 ∧ Matrix.vecMul uW1 (uA 16) = uCt • uW1)
    ∧ (∀ j : Fin 5, Matrix.vecMul uW1 (uA (17 + j.val)) = uW1)
    ∧ (∀ j : Fin 5, ∃ k : ℕ, w12UOrd (17 + j.val) = 2 ^ k)
    ∧ (∀ i : Fin 33, 0 < w12UOrd i.val)
    ∧ (∀ k ∈ w12UNormIdx, ∀ i : Fin 4, uVec (w12UConjCode k i.val) = fun r => uA k r i) :=
  ⟨CertificateChecks.Batch38956.uA_mul_uAInv, CertificateChecks.Batch38956.card_cls_zero, CertificateChecks.Batch38956.card_cls_one,
    CertificateChecks.Batch38956.tree_spec, CertificateChecks.Batch38956.uW1_spec, CertificateChecks.Batch38956.uW_spec, CertificateChecks.Batch38956.uCr_spec,
    CertificateChecks.Batch38956.uCt_spec, CertificateChecks.Batch38956.uP_fix, CertificateChecks.Batch38956.ord_p, CertificateChecks.Batch38956.ord_pos,
    CertificateChecks.Batch38956.uVec_conjCode⟩

end Certificates
