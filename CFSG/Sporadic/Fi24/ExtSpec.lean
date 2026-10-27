
module

public import CFSG.Sporadic.Fi24.ExtSpecBase

public import CFSG.Sporadic.Fi24.ExtCert

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Fi24

open CFSG.F3.Native Native Matrix CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm
  CFSG.Perm.Native

theorem extFacts : ExtFacts := by
  have h := ext_certificate
  unfold extChecks at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

theorem genFacts :
    ∀ j < 13, canonRows 781 sgW[j]! = true ∧ canonRows 781 sgiW[j]! = true ∧
    eqRows 781 (mulW sgW[j]! sgiW[j]!) (idW 781) = true := by
  have h := extFacts.gens
  unfold genChecks at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  intro j hj
  exact ⟨(h.2 j hj).1.1, (h.2 j hj).1.2, (h.2 j hj).2⟩

theorem matW_sg :
    ∀ j < 13, matW 781 781 sgW[j]! = mat (gs j) ∧
    matW 781 781 sgiW[j]! = mat (gs j)⁻¹ := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    obtain ⟨hc, hci, he⟩ := genFacts j hj
    have hG : matW 781 781 sgW[j]! = mat (gs j) := by
      rw [show sgW[j]! = (slpMatsN chainWords (j + 1)).1[j]! from (slpMatsN_get _ 13 hj).1,
        slpMatsN_succ]
      have hletter : ∀ z ∈ chainWords[j]!, LetterOK
          (chainLetterW (slpMatsN chainWords j).1 (slpMatsN chainWords j).2 z)
          (mat (if z.natAbs ≤ 2 then genG z else if z.natAbs - 3 < j then
            (if 0 < z then gs (z.natAbs - 3) else (gs (z.natAbs - 3))⁻¹) else 1)) := by
        intro z hz
        obtain ⟨hz0, hzr⟩ := slpOK_letter (by rw [chainWords_size]; exact hj) hz
        by_cases h2 : z.natAbs ≤ 2
        · rw [ite_eq_left h2]
          have : z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2 := by omega
          rcases this with rfl | rfl | rfl | rfl
          · rw [chainLetterW_one, genG_one]
            exact letterOK_matA
          · rw [chainLetterW_neg_one, genG_neg_one, a_inv]
            exact letterOK_matA
          · rw [chainLetterW_two, genG_two]
            exact letterOK_matB
          · rw [chainLetterW_neg_two, genG_neg_two, mat_b_inv]
            exact letterOK_matB.mulW letterOK_matB
        · rw [ite_eq_right h2]
          have hlt : z.natAbs - 3 < j := by omega
          rw [ite_eq_left hlt]
          have hget := slpMatsN_get chainWords (j := z.natAbs - 3) j hlt
          have hget13 := slpMatsN_get chainWords (j := z.natAbs - 3) 13 (by omega)
          obtain ⟨ihG, ihGi⟩ := ih _ hlt (by omega)
          obtain ⟨hc', hci', -⟩ := genFacts (z.natAbs - 3) (by omega)
          have hne1 : ¬(z = 1 ∨ z = -1) := by omega
          have hne2 : ¬z = 2 := by omega
          have hne3 : ¬z = -2 := by omega
          unfold chainLetterW
          rw [ite_eq_right hne1, ite_eq_right hne2, ite_eq_right hne3]
          by_cases hpos : 0 < z
          · rw [ite_eq_left hpos, ite_eq_left hpos, getD_eq_getElem!, hget.1, ← hget13.1]
            exact ⟨(LetterOK.of_canonRows hc').wf, (LetterOK.of_canonRows hc').size, ihG⟩
          · rw [ite_eq_right hpos, ite_eq_right hpos, getD_eq_getElem!, hget.2, ← hget13.2]
            exact ⟨(LetterOK.of_canonRows hci').wf, (LetterOK.of_canonRows hci').size, ihGi⟩
      rw [(wordW_spec _ hletter).mat, gs, CFSG.Sporadic.Fi23.slpG_eq, mat_wordG]
      rfl
    refine ⟨hG, mat_inv_eq ?_⟩
    have := congrArg (matW 781 781) (eq_of_eqRows he).2
    rwa [matW_mulW (m := 781) (by norm_num) (LetterOK.of_canonRows hc).wf
      (LetterOK.of_canonRows hci).wf (by rw [(canonRows_spec hci).1]), matW_idW (by norm_num),
      hG] at this

theorem letterOK_genLetter
    {z : ℤ} (h13 : z.natAbs ≤ 13) :
    LetterOK (genLetterW sgW sgiW z) (mat (genLetterG z)) := by
  have hlt : z.natAbs - 1 < 13 := by omega
  obtain ⟨hc, hci, -⟩ := genFacts (z.natAbs - 1) hlt
  obtain ⟨hG, hGi⟩ := matW_sg (z.natAbs - 1) hlt
  unfold genLetterW genLetterG
  by_cases hpos : 0 < z
  · rw [ite_eq_left hpos, ite_eq_left hpos, getD_eq_getElem!]
    exact ⟨(LetterOK.of_canonRows hc).wf, (LetterOK.of_canonRows hc).size, hG⟩
  · rw [ite_eq_right hpos, ite_eq_right hpos, getD_eq_getElem!]
    exact ⟨(LetterOK.of_canonRows hci).wf, (LetterOK.of_canonRows hci).size, hGi⟩

theorem letterOK_extWord
    {w : List ℤ} (hw : ∀ z ∈ w, z.natAbs ≤ 13) :
    LetterOK (wordW (genLetterW sgW sgiW) w) (mat (extWord w)) := by
  have := wordW_spec w (fun z hz => letterOK_genLetter (hw z hz))
  rwa [← mat_wordG] at this

theorem baseFacts : BaseFacts := by
  have h := extFacts.base
  unfold baseChecks at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem mS_mul_mK : mS * mK = 1 := by
  have h := congrArg (matW 253 253) (eq_of_eqRows baseFacts.SK).2
  rwa [matW_mulW (m := 253) (by norm_num) (RowsWF.of_canonRows baseFacts.S_canon) rowsWF_gramW
    (by rw [gramW_size]), matW_gramW, matW_idW (by norm_num)] at h

theorem mK_mul_mS : mK * mS = 1 := by
  have h := congrArg (matW 253 253) (eq_of_eqRows baseFacts.KS).2
  rwa [matW_mulW (m := 253) (by norm_num) rowsWF_gramW (RowsWF.of_canonRows baseFacts.S_canon)
    (by rw [(canonRows_spec baseFacts.S_canon).1]), matW_gramW, matW_idW (by norm_num)] at h

theorem rowsWF_orthoProj :
    RowsWF (orthoProj 253 rootForm.rows matF gramInvW) :=
  RowsWF.mulW (RowsWF.transposeW (by norm_num) _ _)
    (RowsWF.mulW (RowsWF.of_canonRows baseFacts.S_canon)
      (RowsWF.mulW rootForm_facts.2 matrixFacts.F_wf))

theorem matW_orthoProj :
    matW 781 781 (orthoProj 253 rootForm.rows matF gramInvW) = mE := by
  obtain ⟨hRs, hRw⟩ := rootForm_facts
  have hFw := matrixFacts.F_wf
  have hFs := matrixFacts.F_size
  have hSw := RowsWF.of_canonRows baseFacts.S_canon
  have hSs := (canonRows_spec baseFacts.S_canon).1
  have hRF : matW 253 781 (mulW rootForm.rows matF) = mR * mF :=
    matW_mulW (m := 781) (by norm_num) hRw hFw (by omega)
  have hRFw : RowsWF (mulW rootForm.rows matF) := RowsWF.mulW hRw hFw
  unfold orthoProj
  rw [matW_mulW (m := 253) (by norm_num) (RowsWF.transposeW (by norm_num) _ _)
    (RowsWF.mulW hSw hRFw) (by rw [mulW_size, hSs]), matW_transposeW (by norm_num) hRw,
    matW_mulW (m := 253) (by norm_num) hSw hRFw (by rw [mulW_size, hRs]), hRF]

theorem matW_matT :
    matW 781 781 matTW = mT := by
  rw [matTW, matT, matW_addW (RowsWF.idW (by norm_num)) rowsWF_orthoProj, matW_idW (by norm_num),
    matW_orthoProj]

theorem letterOK_matT :
    LetterOK matTW mT :=
  ⟨RowsWF.of_canonRows baseFacts.T_canon, (canonRows_spec baseFacts.T_canon).1, matW_matT⟩

end CFSG.Sporadic.Fi24
