module

public import Certificates.Kernel.CF23L34.HeGSR1
public import Certificates.Kernel.LocalComp.HeGS36Glue
public import CFSG.Certificates.Kernel.CF23L34.RegRunSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.HeGSR

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.PermTool
open CFSG.KC.CF23L34 CFSG.PSL3Four.Native CFSG.Monster.B.Co2.Native CFSG.Sporadic.HeldB
open CFSG.Sporadic.SmallOddCore CFSG.ComponentClassification.GrSLit.HeldFix
open CFSG.ComponentClassification.GrSLit.HeGS
open CertificateChecks.KernelLC.HeFix CertificateChecks.KernelLC.HeGS36

theorem ew_lt (k : Nat) : (∀ j ∈ ew k, j < 9) ∧ ∀ j ∈ (ew k).reverse, j < 9 := by
  have h : ∀ i < 5, ∀ j ∈ heDWords.getD i [], j < 9 := by decide
  have h1 : ∀ j ∈ ew k, j < 9 := h (k % 5) (Nat.mod_lt _ (by decide))
  exact ⟨h1, fun j hj => h1 j (List.mem_reverse.mp hj)⟩

theorem gParts : cn gT = true ∧ cn gI = true ∧
    invCand 8330 heGSGTab = unpack 8330 14 gI ∧
    permOK 8330 14 (mask 14) (8330 * 14) gT gI = true ∧
    permOK 8330 14 (mask 14) (8330 * 14) gI gT = true := by
  have h := kC
  simp only [Bool.and_eq_true] at h
  refine ⟨parts.2.2.2.2.1, parts.2.2.2.2.2, ?_, h.1.2, h.2⟩
  rw [gTab]
  exact (invEqK_sound h.1.2).1

theorem init_rel : RegRel (unpack 8330 14) (fun p => cn p = true) R0 heGSInit := by
  obtain ⟨cg, cgi, hgi, -, -⟩ := gParts
  refine ⟨by simp [heGSInit, R0], fun i hi => ?_⟩
  have hi10 : i < 10 := by simpa [R0] using hi
  have e1 : heGSInit[i]! = (if i < 5 then (heGSKTab (ew i), heGSKTab (ew i).reverse) else
      (comp 8330 (comp 8330 heGSGTab (heGSKTab (ew i))) (invCand 8330 heGSGTab),
        comp 8330 (comp 8330 heGSGTab (heGSKTab (ew i).reverse)) (invCand 8330 heGSGTab))) := by
    rw [heGSInit, ofFn_get _ hi10]
    rfl
  have e2 : R0[i]'hi = (if i < 5 then (K (ew i), K (ew i).reverse)
      else (pc (pc gT (K (ew i))) gI, pc (pc gT (K (ew i).reverse)) gI)) := by
    simp only [R0, List.getElem_map, List.getElem_range]
  obtain ⟨l1, l2⟩ := ew_lt i
  have k1 := kw l1
  have k2 := kw l2
  rw [e1]
  simp only [e2]
  by_cases h5 : i < 5
  · simp only [if_pos h5]
    exact ⟨by rw [k1.1, k2.1], k1.2, k2.2⟩
  · simp only [if_neg h5]
    refine ⟨?_, cnpc (cnpc cg k1.2) cgi, cnpc (cnpc cg k2.2) cgi⟩
    rw [hgi, gTab, k1.1, k2.1, cmp cg k1.2, cmp (cnpc cg k1.2) cgi, cmp cg k2.2,
      cmp (cnpc cg k2.2) cgi]

theorem pc_id {p : Nat} (hp : cn p = true) : pc p (pidn 8330 14) = p := by
  have hsz := CFSG.KC.L34KSnd.canon_sz hp
  exact CFSG.KC.L34KSnd.eq_of_pg (canonK_pcomp hp (CFSG.KC.L34KSnd.canon_pidn hsz)) hp
    fun i hi => by rw [pc, CFSG.KC.L34KSnd.pg_pcomp' hp hi, CFSG.KC.L34KSnd.pg_pidn' hsz hi]

theorem id_pc {p : Nat} (hp : cn p = true) : pc (pidn 8330 14) p = p := by
  have hsz := CFSG.KC.L34KSnd.canon_sz hp
  exact CFSG.KC.L34KSnd.eq_of_pg (canonK_pcomp (CFSG.KC.L34KSnd.canon_pidn hsz) hp) hp
    fun i hi => by
      rw [pc, CFSG.KC.L34KSnd.pg_pcomp' (CFSG.KC.L34KSnd.canon_pidn hsz) hi,
        CFSG.KC.L34KSnd.pg_pidn' hsz (CFSG.KC.L34KSnd.canon_lt hp hi)]

theorem check22702 :
    heGSOK 10 heGSProg = true ∧ permChk 8330 heGSGTab = true ∧
      comp 8330 heGSGTab (heGen 0) = comp 8330 heGSVTab heGSGTab ∧
      (heGSRun 8330 heGSInit heGSProg)[133]!.1 = heGen 0 ∧
      (heGSRun 8330 heGSInit heGSProg)[134]!.1 = heGen 1 := by
  have hok : heGSOK 10 heGSProg = true := by decide
  obtain ⟨cg, -, -, p1, p2⟩ := gParts
  have hlen : R0.length = 10 := by simp [R0]
  have hrel := run_rel (n := 8330) (φ := unpack 8330 14) (m := pc) (e := pidn 8330 14)
    (C := fun p => cn p = true) (fun p q hp hq => cmp hp hq) (fun p q hp hq => cnpc hp hq)
    (by rw [idTab_eq, hidA]) hid (fun p hp => pc_id hp) (fun p hp => id_pc hp) heGSProg init_rel
    (by rw [hlen]; exact hok)
  have i134 : 134 < (rRun1 pc (pidn 8330 14) R0 heGSProg).length := by
    rw [rRun_length, hlen]
    all_goals decide
  have i133 : 133 < (rRun1 pc (pidn 8330 14) R0 heGSProg).length := by omega
  have hr := ch22702_run
  simp only [Bool.and_eq_true] at hr
  have r133 := (hrel.2 133 i133).1
  have r134 := (hrel.2 134 i134).1
  rw [← getD_lt i133 (0, 0)] at r133
  rw [← getD_lt i134 (0, 0)] at r134
  have kv := kw (w := heGSVWord) (by decide)
  refine ⟨hok, CertificateChecks.KernelSporSch.HePt.perm_of gTab p1 p2, ?_, ?_, ?_⟩
  · rw [gTab, heGen_eq (k := 0) (by decide), heGSVTab, kv.1, cmp cg cnG.1, cmp kv.2 cg,
      Nat.eq_of_beq_eq_true ch22702_g]
  · rw [r133, Nat.eq_of_beq_eq_true hr.1, heGen_eq (k := 0) (by decide)]
  · rw [r134, Nat.eq_of_beq_eq_true hr.2, heGen_eq (k := 1) (by decide)]

end CertificateChecks.KernelLC.HeGSR

end
