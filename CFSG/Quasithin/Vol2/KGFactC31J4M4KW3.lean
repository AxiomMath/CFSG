module

public import CFSG.Quasithin.Vol2.KGFactC31J4M4F

public section

namespace CFSG.Quasithin.KGC31.J4M4

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Quasithin.KGC31
open CFSG.Quasithin.KGC31.J4
open scoped Matrix

theorem chkKW_true : chkKW () = true :=
  Certificates.certificate7253.2

@[expose] noncomputable def gJ : G₀ := wordProd baseJ gWord

@[expose] noncomputable def kwRow (k : ℕ) : Row := toRow (kwVecs.getD k V2.zero).toVec

section Chk

variable (hc : chkKW () = true)
include hc

theorem chkKW_parts :
    frApply (frTable (wordRows baseMats baseInvs gWord)) rootV = kwVecs.getD 0 V2.zero ∧
      ∀ l < 4, ∀ k < 31, frApply (frTable ((letRows ())[l]?.getD idRows)) (kwVecs.getD k V2.zero) =
        kwVecs.getD ((kwSig.getD l []).getD k 0) V2.zero := by
  have h := hc
  unfold chkKW at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  exact h

variable (hM : MatFacts)
include hM

theorem kwRow_zero : kwRow 0 = gJ⁻¹ • CFSG.Sporadic.J4.QT2.w₀ := by
  obtain ⟨h1, -⟩ := chkKW_parts hc
  apply ofRow_inj.mp
  rw [inv_smul_row, ← Mx_apply, gJ, Mx_wordProd_baseJ hM]
  show (kwVecs.getD 0 V2.zero).toVec = rootV.toVec ᵥ* _
  rw [← h1, frApply_toVec_eq_vecMul]

theorem m4gen_smul_kwRow {l : ℕ} (hl : l < 2) {k : ℕ} (hk : k < 31) :
    m4gen l • kwRow k = kwRow ((kwSig.getD l []).getD k 0) := by
  obtain ⟨-, h2⟩ := chkKW_parts hc
  have e := h2 l (by omega) k hk
  have hl' : (letRows ())[l]?.getD idRows = (m4Invs ())[l]?.getD idRows := by
    rcases (show l = 0 ∨ l = 1 by omega) with rfl | rfl
    · simp only [letRows, List.getElem?_toArray, List.getElem?_cons_zero, Option.getD_some]
    · simp only [letRows, List.getElem?_toArray, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.getD_some]
  apply ofRow_inj.mp
  rw [smul_row]
  show (kwVecs.getD k V2.zero).toVec ᵥ* _ =
    (kwVecs.getD ((kwSig.getD l []).getD k 0) V2.zero).toVec
  rw [← e, frApply_toVec_eq_vecMul, hl', m4Invs_spec hM]
  rfl

end Chk

end CFSG.Quasithin.KGC31.J4M4

end
