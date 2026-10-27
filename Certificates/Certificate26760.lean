module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Model.Tables
import Certificates.Kernel.HN1408.C26760
import Certificates.Kernel.HN1408.Glue
import Certificates.Kernel.TwoHS.HarGlue

namespace CertificateChecks.Batch26760

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH CFSG.KD.HN1408
open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.TwoHS
open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Recognition.HSMultiplier

theorem x_parts (i : Fin 6) : h1408X i = tabT (unpack 1408 11 (X8 i)) ∧ Cn (X8 i) :=
  ⟨h1408T_eq (by have := i.isLt; omega), (h8 (j := i.val) (by have := i.isLt; omega)).1⟩

theorem xi_parts (i : Fin 6) : h1408XI i = tabT (unpack 1408 11 (X8 i)) ∧ Cn (X8 i) := by
  refine ⟨?_, (x_parts i).2⟩
  unfold h1408XI
  rw [(x_parts i).1]
  exact invT_unpack (by norm_num) (h8 (j := i.val) (by have := i.isLt; omega)).2

theorem ev_parts (wd : List (Fin 6 × Bool)) :
    evalW 1408 h1408X h1408XI wd = tabT (unpack 1408 11 (EV8 wd)) ∧ Cn (EV8 wd) := by
  unfold evalW EV8
  rw [idT_eq]
  exact CFSG.KD.TwoHS.evalW_foldlG x_parts xi_parts wd idK cId

theorem v_eq : h1408V = tabT (unpack 1408 11 V8) := h1408T_eq (by norm_num)

theorem cV : Cn V8 := (h8 (j := 6) (by norm_num)).1

theorem perm_ok : h1408PermOK = true := by
  have c1 : (List.finRange 6).all (fun i =>
      permOK 1408 (h1408X i) && invOK 1408 (h1408X i) (h1408XI i)) = true := by
    rw [List.all_eq_true]
    intro i _
    unfold h1408XI
    rw [(x_parts i).1]
    exact gen_ok (j := i.val) (by have := i.isLt; omega)
  have h := block26760
  simp only [bAnd_iff] at h
  unfold h1408PermOK
  rw [c1, v_eq, permOK_unpack cV (h8 (j := 6) (by norm_num)).2, invoOK_eq cV, h.2.2]
  rfl

theorem rel_ok : h1408RelOK = true := by
  have c2 : hsRels.all (fun r => (List.finRange 6).all fun i =>
      commTT 1408 (h1408X i) (evalW 1408 h1408X h1408XI r)) = true := by
    rw [List.all_eq_true]
    intro r hr
    rw [List.all_eq_true]
    intro i _
    obtain ⟨e, c⟩ := ev_parts r
    rw [e, (x_parts i).1, commTT_eq (x_parts i).2 c]
    exact List.all_eq_true.1 (List.all_eq_true.1 rel26760 r hr) i (List.mem_finRange i)
  have c3 : (List.finRange 6).all (fun i =>
      tblEq 1408 (evalW 1408 h1408X h1408XI (hsCommWord i)) (h1408X i)) = true := by
    rw [List.all_eq_true]
    intro i _
    obtain ⟨e, c⟩ := ev_parts (hsCommWord i)
    rw [e, (x_parts i).1, tblEq_eq c (x_parts i).2]
    exact List.all_eq_true.1 comm26760 i (List.mem_finRange i)
  unfold h1408RelOK
  rw [c2, c3]
  rfl

theorem xs_getD {l : Nat} (h1 : 1 ≤ l) (h6 : l ≤ 6) :
    h1408Xs.getD (l - 1) (idT 1408) = tabT (unpack 1408 11 (L l)) ∧ Cn (L l) := by
  have hl : l - 1 < 6 := by omega
  have e : h1408Xs.getD (l - 1) (idT 1408) = h1408T (l - 1) := by
    simp [h1408Xs, List.getD_eq_getElem?_getD, hl, h1408X]
  rw [e, h1408T_eq (by omega)]
  exact ⟨rfl, (h8 (by omega)).1⟩

theorem sig_letters : ∀ j < 6, ∀ l ∈ sigWords.getD j [], 1 ≤ l ∧ l ≤ 6 := by decide

theorem sigma_ok : h1408SigmaOK = true := by
  unfold h1408SigmaOK
  rw [List.all_eq_true]
  intro i _
  obtain ⟨e, c⟩ := wordTbl_unpack (wd := sigWords.getD i.val []) idT_eq cId fun l hl =>
    xs_getD (sig_letters i.val i.isLt l hl).1 (sig_letters i.val i.isLt l hl).2
  have cx := (x_parts i).2
  rw [v_eq, (x_parts i).1, conjT_unpack cV cV cx, e,
    tblEq_eq (CFSG.KC.BfsPin.canonK_pcomp (CFSG.KC.BfsPin.canonK_pcomp cV cx) cV) c]
  exact List.all_eq_true.1 sigma26760 i (List.mem_finRange i)

theorem central_ok : h1408CentralOK = true := by
  have h := central26760
  rw [bAnd_iff] at h
  obtain ⟨e, c⟩ := ev_parts h1408R25
  unfold h1408CentralOK h1408T25
  rw [e, involOK_eq c, h.1, Bool.true_and, List.all_eq_true]
  intro p hp
  have hp' := List.mem_range.1 hp
  have h2 := allN_spec h.2 p hp'
  rw [ap_eq c hp', bne_iff_ne]
  intro ep
  rw [ep, Nat.beq_refl] at h2
  exact absurd h2 (by decide)

theorem block_ok : h1408BlockOK = true := by
  have h := block26760
  simp only [bAnd_iff] at h
  obtain ⟨hh, hs, -⟩ := h
  unfold h1408BlockOK
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  refine ⟨fun i _ => ?_, fun k hk => ?_⟩
  · have hi := allN_spec hh i.val i.isLt
    rw [(x_parts i).1, Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · have hk' := List.mem_range.1 hk
      have h' := allN_spec hi k hk'
      simp only [bAnd_iff, Nat.blt_eq, Nat.ble_eq] at h'
      rw [ap_eq (x_parts i).2 (by omega)]
      exact decide_eq_true h'.1
    · have hk' := List.mem_range.1 hk
      have h' := allN_spec hi k hk'
      simp only [bAnd_iff, Nat.blt_eq, Nat.ble_eq] at h'
      rw [ap_eq (x_parts i).2 (by omega)]
      exact decide_eq_true h'.2
  · have hk' := List.mem_range.1 hk
    have h' := allN_spec hs k hk'
    simp only [bAnd_iff] at h'
    rw [v_eq, ap_eq cV (by omega), ap_eq cV (by omega), Nat.eq_of_beq_eq_true h'.1,
      Nat.eq_of_beq_eq_true h'.2]
    simp

end CertificateChecks.Batch26760

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.HNRecog in
theorem certificate26760 : h1408PermOK = true ∧ h1408RelOK = true ∧ h1408SigmaOK = true ∧
    h1408CentralOK = true ∧ h1408BlockOK = true :=
  ⟨CertificateChecks.Batch26760.perm_ok, CertificateChecks.Batch26760.rel_ok, CertificateChecks.Batch26760.sigma_ok, CertificateChecks.Batch26760.central_ok,
    CertificateChecks.Batch26760.block_ok⟩

end Certificates
