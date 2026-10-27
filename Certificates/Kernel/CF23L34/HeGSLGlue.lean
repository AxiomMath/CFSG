module

public import Certificates.Kernel.CF23L34.HeGSL
public import Certificates.Kernel.LocalComp.HeGS36Glue
public import Certificates.Kernel.Sporadic.OddCore.HLF

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.HeGSL

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.PermTool
open CFSG.PSL3Four.Native CFSG.Monster.B.Co2.Native CFSG.Sporadic.HeldB
open CFSG.Sporadic.SmallOddCore CFSG.ComponentClassification.GrSLit.HeldFix
open CFSG.ComponentClassification.GrSLit.HeGS CertificateChecks.KernelLC.HeFix
open CertificateChecks.KernelLC.HeGS36 CertificateChecks.KernelSpor

theorem hidT : idTab 8330 = unpack 8330 14 (pidn 8330 14) := by rw [idTab_eq, hidA]

theorem ne_of {n w p q : Nat} (hp : canonK n w (mask w) (n * w) p = true)
    (hq : canonK n w (mask w) (n * w) q = true) (h : (!Nat.beq p q) = true) :
    unpack n w p ≠ unpack n w q := fun e => by
  rw [CFSG.KC.L34KSnd.unpack_inj' hp hq e, Nat.beq_refl] at h
  exact absurd h (by decide)

theorem fix_eq (p : Nat) : heGSFix (unpack 8330 14 p) = CFSG.KC.HeFixK.fixK 8330 14 p := by
  unfold heGSFix
  exact CFSG.KC.HeFixK.countP_fix 8330 14 p

theorem fixes_of {p : Nat} (h : fixOm p = true) :
    fixesOK 105 (unpack 8330 14 p) heOmega0 = true := by
  unfold fixesOK
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro k hk
  have e := allN_spec h k hk
  simp only [Bool.and_eq_true] at e
  rw [HeL.om_get hk, CFSG.KC.HeFixK.unpack_getElem! (Eq.mp Nat.blt_eq e.1)]
  exact beq_iff_eq.2 (Nat.eq_of_beq_eq_true e.2)

theorem not346_of {p : Nat} (h : not346 p = true) : heGSFix (unpack 8330 14 p) ≠ 346 := by
  rw [fix_eq]
  intro e
  unfold not346 at h
  rw [e] at h
  exact absurd h (by decide)

theorem check22701 :
    (∀ j < 9, comp 8330 (heInnerC0 j) (heInnerC0 j) = idTab 8330) ∧
      heGSKTab (heGSComm2 heGST0Comm) = heGen 0 ∧
      fixesOK 105 (heGen 0) heOmega0 = true ∧
      fixesOK 105 (heGSKTab (heGSComm2 heGSUComm)) heOmega0 = true ∧
      heGSKTab (heGSComm2 heGSUComm) ≠ idTab 8330 ∧
      heGSKTab (heGSComm2 heGSUComm) ≠ heGen 0 ∧
      comp 8330 heGSVTab heGSVTab = idTab 8330 ∧ heGSVTab ≠ idTab 8330 ∧
      heGSFix heGSVTab = 346 ∧ heGSFix (heGSKTab (heDWords.getD 1 [])) ≠ 346 ∧
      heGSFix (heGSKTab (heGSComm2 heGSUComm ++ heDWords.getD 1 [])) ≠ 346 ∧
      heGSFix (heGSKTab (0 :: (heGSComm2 heGSUComm ++ heDWords.getD 1 []))) ≠ 346 ∧
      comp 8330 (heGSKTab (heDWords.getD 0 [])) heGSVTab ≠
        comp 8330 heGSVTab (heGSKTab (heDWords.getD 0 [])) ∧
      comp 8330 (heGSKTab (heDWords.getD 0 [])) (heGSKTab (heDWords.getD 1 [])) ≠
        comp 8330 (heGSKTab (heDWords.getD 1 [])) (heGSKTab (heDWords.getD 0 [])) ∧
      ∀ l ∈ [2, 3, 4, 5, 6, 7, 8, 9], comp 105 (heGSDRep l) (heGSDRep l) ≠ idTab 105 := by
  have hT := ch22701_t0
  have hU := ch22701_u
  have hV := ch22701_v
  have hF := ch22701_fix
  have hC := ch22701_comm
  simp only [Bool.and_eq_true] at hT hU hV hF hC
  have kt := kw (w := heGSComm2 heGST0Comm) (by decide)
  have ku := kw (w := heGSComm2 heGSUComm) (by decide)
  have kv := kw (w := heGSVWord) (by decide)
  have k0 := kw (w := heDWords.getD 0 []) (by decide)
  have k1 := kw (w := heDWords.getD 1 []) (by decide)
  have g0 := heGen_eq (k := 0) (by decide)
  have hv : heGSVTab = unpack 8330 14 (K heGSVWord) := by rw [heGSVTab, kv.1]
  refine ⟨fun j hj => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun l hl => ?_⟩
  · have c := parts.1 j hj
    rw [(CertificateChecks.KernelSporSch.HeB14.C0_word hj).1, cmp c c,
      Nat.eq_of_beq_eq_true (allN_spec ch22701_c0 j hj), hidT]
  · rw [kt.1, g0, Nat.eq_of_beq_eq_true hT.1]
  · rw [g0]
    exact fixes_of hT.2
  · rw [ku.1]
    exact fixes_of hU.1.1
  · rw [ku.1, hidT]
    exact ne_of ku.2 hid hU.1.2
  · rw [ku.1, g0]
    exact ne_of ku.2 cnG.1 hU.2
  · rw [hv, cmp kv.2 kv.2, Nat.eq_of_beq_eq_true hV.1.1, hidT]
  · rw [hv, hidT]
    exact ne_of kv.2 hid hV.1.2
  · rw [hv, fix_eq]
    exact Nat.eq_of_beq_eq_true hV.2
  · rw [k1.1]
    exact not346_of hF.1.1
  · rw [(kw (by decide)).1]
    exact not346_of hF.1.2
  · rw [(kw (by decide)).1]
    exact not346_of hF.2
  · rw [hv, k0.1, cmp k0.2 kv.2, cmp kv.2 k0.2]
    exact ne_of (cnpc k0.2 kv.2) (cnpc kv.2 k0.2) hC.1
  · rw [k0.1, k1.1, cmp k0.2 k1.2, cmp k1.2 k0.2]
    exact ne_of (cnpc k0.2 k1.2) (cnpc k1.2 k0.2) hC.2
  · have hl' : 2 ≤ l ∧ l < 10 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      omega
    have h := allN_spec ch22701_reps (l - 2) (by omega)
    have e : Nat.add (l - 2) 2 = l := by
      rw [Nat.add_eq]
      omega
    rw [e] at h
    have r := HeL.root_canon hl'.2
    unfold heGSDRep
    rw [HeL.rep_eq hl'.2, HeL.comp105 r r, HeL.idTab_eq]
    exact ne_of (CFSG.KC.BfsPin.canonK_pcomp r r) HeL.base.2.1 h

end CertificateChecks.KernelLC.HeGSL

end
