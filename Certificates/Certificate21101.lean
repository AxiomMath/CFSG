module

public import Certificates.Kernel.OmegaEight.Bridge3009
public import Certificates.Kernel.OmegaEight.DW27K
public import Certificates.Certificate3119

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.EvenSmallLie.OmegaEight
  CFSG.Monster.B.Co2.Native CFSG.LargeExtraspecial.DW.Insp

theorem dw_cnAP {i : Nat} (hi : i < 10) : cn (AP.S i) = true := by
  have h := kStrC
  simp only [bAnd_iff] at h
  exact allN_spec h.1 i hi

theorem dw_rel : Nat.beq (ppw (AP.S 8) 3) pid = true ∧ Nat.beq (pc (AP.S 9) (AP.S 9)) pid = true ∧
    Nat.beq (pc (AP.S 9) (AP.S 8)) (pc (ppw (AP.S 8) 2) (AP.S 9)) = true ∧
    allN 3 (fun k => cn (ppw (AP.S 8) k)) = true := by
  have h := kRel
  simp only [bAnd_iff] at h
  exact h

theorem dw_a {i : Nat} (hi : i < 4) :
    lettersK 17 (eWords.getD i []) = true ∧ cn (dwA i) = true ∧ Nat.beq (ppw (dwA i) 3) pid = true ∧
      allN 3 (fun k => cn (ppw (dwA i) k)) = true ∧
      allN 4 (fun j => Nat.beq (pc (dwA i) (dwA j)) (pc (dwA j) (dwA i))) = true := by
  have h := kE
  simp only [bAnd_iff] at h
  have h1 := allN_spec h.1 i hi
  simp only [bAnd_iff] at h1
  exact h1

theorem dw_aArr {i : Nat} (hi : i < 4) : aArr i = unpack 360 9 (dwA i) :=
  omegaW_eq (dw_a hi).1

theorem dw_term (t : List Nat) (ht : t.all (fun i => Nat.blt i 4) = true) :
    termArr t = unpack 360 9 (dwT t) ∧ cn (dwT t) = true := by
  induction t with
  | nil => exact ⟨idA_eq, cn_pid⟩
  | cons i t ih =>
    simp only [List.all_cons, Bool.and_eq_true] at ht
    have hi : i < 4 := Nat.le_of_ble_eq_true ht.1
    obtain ⟨e, c⟩ := ih ht.2
    have ca := (dw_a hi).2.1
    have et : termArr (i :: t) = compA 360 (aArr i) (termArr t) := rfl
    have ek : dwT (i :: t) = pc (dwA i) (dwT t) := rfl
    rw [et, ek, e, dw_aArr hi, compA_pc ca c]
    exact ⟨rfl, cn_pc ca c⟩

theorem dw_conj {k : Nat} (hk : k < 3) {w : List Int} (hw : lettersK 17 w = true)
    (hc : cn (wO w) = true) : bwConj k w = unpack 360 9 (dwC k w) ∧ cn (dwC k w) = true := by
  have hp := allN_spec dw_rel.2.2.2 k hk
  unfold bwConj dwC
  rw [omegaW_eq hw, gen_get (by norm_num), powArr_pc (dw_cnAP (by norm_num)), compA_pc hc hp]
  exact ⟨rfl, cn_pc hc hp⟩

theorem dw_relCheck : relCheck = true := by
  obtain ⟨h3, h2, hc, hp⟩ := dw_rel
  have c8 := dw_cnAP (by norm_num : 8 < 10)
  have c9 := dw_cnAP (by norm_num : 9 < 10)
  have p2 := allN_spec hp 2 (by norm_num)
  unfold relCheck
  rw [gen_get (by norm_num), gen_get (by norm_num), powArr_pc c8, powArr_pc c8,
    Nat.eq_of_beq_eq_true h3, idA_eq, compA_pc c9 c9, compA_pc c9 c8, compA_pc p2 c9,
    eqA_pc cn_pid cn_pid, eqA_pc (cn_pc c9 c9) cn_pid, eqA_pc (cn_pc c9 c8) (cn_pc p2 c9), h2, hc,
    Nat.beq_refl]
  rfl

theorem dw_eCheck : eCheck = true := by
  have h := kE
  simp only [bAnd_iff] at h
  obtain ⟨-, hne, h0, h1⟩ := h
  have c9 := dw_cnAP (by norm_num : 9 < 10)
  obtain ⟨et, ct⟩ := dw_term [0, 1, 2] rfl
  unfold eCheck
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨fun i hi => ⟨?_, fun j hj => ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · obtain ⟨-, ca, h3, -, -⟩ := dw_a hi
    rw [dw_aArr hi, powArr_pc ca, Nat.eq_of_beq_eq_true h3, idA_eq, eqA_pc cn_pid cn_pid,
      Nat.beq_refl]
  · obtain ⟨-, ca, -, -, hcm⟩ := dw_a hi
    rw [dw_aArr hi, dw_aArr hj, commArr_pc ca (dw_a hj).2.1]
    exact allN_spec hcm j hj
  · rw [et, idA_eq, eqA_pc ct cn_pid]
    exact not_beq_of hne
  · rw [gen_get (by norm_num), dw_aArr (by norm_num), commArr_pc c9 (dw_a (by norm_num)).2.1]
    exact h0
  · rw [gen_get (by norm_num), dw_aArr (by norm_num), commArr_pc c9 (dw_a (by norm_num)).2.1]
    exact h1

theorem dw_bwCheck : bwCheck = true := by
  unfold bwCheck
  rw [List.all_eq_true]
  intro e he
  have h := List.all_eq_true.1 kBW e he
  simp only [bAnd_iff] at h
  obtain ⟨ht, hr, hk, hs, hw, hc, hpc, heq⟩ := h
  obtain ⟨et, ct⟩ := dw_term e.1 ht
  obtain ⟨er, cr⟩ := dw_term _ hr
  obtain ⟨ec, cc⟩ := dw_conj (Nat.le_of_ble_eq_true hk) hw hc
  rw [ec, et, er, powArr_pc cr, compA_pc cc ct, compA_pc hpc cc,
    eqA_pc (cn_pc cc ct) (cn_pc hpc cc)]
  exact heq

theorem dw_invCheck : invCheck = true := by
  unfold invCheck
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true]
  intro i hi
  have h := allN_spec kInv i hi
  simp only [bAnd_iff] at h
  obtain ⟨hl1, hl2, hc1, hc2, hr, heq, hinv⟩ := h
  obtain ⟨em, cm, -⟩ := main_ok (by omega : i < 5)
  obtain ⟨er, cr⟩ := dw_term _ hr
  rw [omegaW_eq hl1, omegaW_eq hl2, er, em, compA_pc hc1 hc2, compA_pc cr hc1,
    eqA_pc (cn_pc hc1 hc2) (cn_pc cr hc1), compA_pc cm hc2, compA_pc hc2 (cn_pc cm hc2),
    compA_pc cm (cn_pc hc2 (cn_pc cm hc2)), idA_eq,
    eqA_pc (cn_pc cm (cn_pc hc2 (cn_pc cm hc2))) cn_pid]
  exact ⟨heq, hinv⟩

theorem dw27_k : dw27Check = true := by
  unfold dw27Check
  rw [dw_relCheck, dw_eCheck, dw_bwCheck, dw_invCheck]
  rfl

end CertificateChecks.KernelO8

namespace Certificates

open CertificateChecks

theorem certificate21101 :
    CFSG.LargeExtraspecial.DW.Insp.dw27Check = true :=
  KernelO8.dw27_k

end Certificates
