module

public import Certificates.Certificate7079
public import CFSG.Quasithin.Recognition.L34AmalgamIsoTab

public section

namespace CFSG.Quasithin.L34Amalgam

open MulAction CFSG.ComponentClassification.WittDesign CFSG.Quasithin.Asc94

theorem evalW_invW {X : Type*} [Group X] (f : Fin 5 → X) (w : List (Fin 5 × Bool)) :
    evalW f (invW w) = (evalW f w)⁻¹ := by
  induction w with
  | nil => simp [invW, evalW]
  | cons x w ih =>
    have e : invW (x :: w) = invW w ++ [(x.1, !x.2)] := by simp [invW]
    rw [e, evalW_append, ih]
    have e2 : evalW f (x :: w) = cond x.2 (f x.1) (f x.1)⁻¹ * evalW f w := by simp [evalW]
    rw [e2, mul_inv_rev]
    rcases x with ⟨i, b⟩
    cases b <;> simp [evalW]

theorem wtabI_eq (s : String) : wtabI genTL genTiL s = tab (evalW gen (word s))⁻¹ := by
  rw [← evalW_invW, tab_evalW]
  unfold wtabI
  simp only [genTL_getD, genTiL_getD]

theorem lettersB_iff {s : String} : lettersB s = true ↔ ∀ x ∈ word s, x.1.val < 3 := by
  simp [lettersB]

theorem a2_ok : a2Check genTL genTiL = true :=
  Certificates.certificate7079.1

theorem pq_ok : pqCheck genTL genTiL crdTL = true :=
  Certificates.certificate7079.2.1

theorem inv_ok : invCheck genTL genTiL crdTL = true :=
  Certificates.certificate7079.2.2.1

theorem conj_ok : conjCheck genTL genTiL = true :=
  Certificates.certificate7079.2.2.2.1

theorem s1_ok : s1Check genTL genTiL = true :=
  Certificates.certificate7079.2.2.2.2.1

theorem rh_ok : rhCheck genTL genTiL = true :=
  Certificates.certificate7079.2.2.2.2.2.1

theorem glue_ok : glueCheck genTL genTiL crdTL = true :=
  Certificates.certificate7079.2.2.2.2.2.2

theorem bWords_length : bWords.length = 192 := by
  decide +kernel

end CFSG.Quasithin.L34Amalgam
