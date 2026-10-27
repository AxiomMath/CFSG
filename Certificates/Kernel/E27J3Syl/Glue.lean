module

public import Certificates.Kernel.E27J3Syl.KB
public import Certificates.Kernel.E27J3Syl.KSW
public import Certificates.Kernel.E27J3Syl.KFP
public import Certificates.Kernel.E27J3Syl.KFU
public import CFSG.Certificates.Kernel.Spor.HKeyUSound
public import Certificates.Kernel.J3Ref.Faith
public import Certificates.Data.Kernel.Spor.HSortB
public import CFSG.Certificates.Kernel.Spor.HKeyBSound
public import Certificates.Kernel.E27J3Syl.KC
public import Certificates.Kernel.E27J3Syl.KE
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue
public import Certificates.Kernel.Sporadic.OddCore.MulHGlue
public import CFSG.Certificates.Kernel.Spor.MulHCaySound
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
import Mathlib.Tactic.IntervalCases
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.BfsPinAlg
import CFSG.Certificates.Kernel.Spor.PcompFacts

public section

set_option maxRecDepth 400000

namespace CFSG.KD.E27J3S

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KS.MulHCay
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.SmallOddCore.Native CFSG.HardMathSupport.Foote.E27 CFSG.Sporadic.Schreier
open CFSG.KS.PEnumB

theorem hnJ : szOK 6156 13 = true := by decide

theorem jiv_spec {p r : Nat} (h : jiv p r = true) :
    jcn p = true ∧ jcn r = true ∧ invEqK 6156 13 (mask 13) (6156 * 13) p r = true := by
  unfold jiv at h
  simp only [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
  exact h

theorem base_parts :
    (∀ k < 8, jiv (SY.F k) (SYI k) = true) ∧
    (∀ k < 2, jiv (CertificateChecks.KernelCensus.J3S.F k) (SGI k) = true) ∧
    jcn jid = true ∧ SE.cnt = 243 ∧ penumHdK jid SE.cnt 300 SE.T SE.PL = true ∧
    (∀ j < 2, SE.GI j = SY.F j ∧ SE.G j = jid ∧ jiv (SE.GI j) (SEI j) = true) ∧
    (∀ c < 2, r32 SEX c < SE.cnt ∧ SE.T (r32 SEX c) = SY.F (2 + 3 * c)) := by
  have h0 := c131001_base
  unfold c131001Base at h0
  simp only [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h0
  obtain ⟨a1, a2, a3, -, a5, a6, a7, a8⟩ := h0
  refine ⟨allN_spec a1, allN_spec a2, a3, Nat.eq_of_beq_eq_true a5, a6, fun j hj => ?_,
    fun c hc => ?_⟩
  · have h := allN_spec a7 j hj
    simp only [Bool.and_eq_true] at h
    obtain ⟨b1, b2, b3⟩ := h
    exact ⟨Nat.eq_of_beq_eq_true b1, Nat.eq_of_beq_eq_true b2, b3⟩
  · have h := allN_spec a8 c hc
    rw [CFSG.KS.Raw.Orb.strictB_eq] at h
    simp only [Bool.and_eq_true] at h
    exact ⟨Nat.le_of_ble_eq_true h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem hcnt : SE.cnt = 243 := base_parts.2.2.2.1

theorem hidc : canonK 6156 13 (mask 13) (6156 * 13) (pidn 6156 13) = true := base_parts.2.2.1

theorem hid : idT 6156 = tabT (unpack 6156 13 (pidn 6156 13)) := by
  rw [idT_tabT, CFSG.KC.BfsPin.idA_eq hnJ]

theorem sy_tab {k : Nat} (hk : k < 8) :
    j3SylTbl k = tabT (unpack 6156 13 (SY.F k)) ∧ canonK 6156 13 (mask 13) (6156 * 13) (SY.F k) =
      true := by
  have h := CFSG.KC.Misc.HexFlat.hexT_sound SY.all (by norm_num) k hk
  rw [← SY.eq] at h
  have e : j3SylTbl k = hexT 4 6156 (6156 * k) j3SylHex := by unfold j3SylTbl; rfl
  refine ⟨?_, (jiv_spec (base_parts.1 k hk)).1⟩
  rw [e, ← h, tabT_natArr]

theorem sy_inv {k : Nat} (hk : k < 8) : permOK 6156 (j3SylTbl k) = true := by
  rw [(sy_tab hk).1]
  exact permOK_unpack (sy_tab hk).2 (jiv_spec (base_parts.1 k hk)).2.2

theorem gen_nat {k : Nat} (hk : k < 2) :
    natArr (hexT 4 6156 (6156 * k) j3StrongHex) =
      unpack 6156 13 (CertificateChecks.KernelCensus.J3S.F k) := by
  have h := CFSG.KC.Misc.HexFlat.hexT_sound CertificateChecks.KernelCensus.J3S.all (by norm_num) k
    (Nat.lt_of_lt_of_le hk (by decide))
  rw [← CertificateChecks.KernelCensus.J3S.eq] at h
  exact h

theorem gen_tab {k : Nat} (hk : k < 2) :
    hexT 4 6156 (6156 * k) j3StrongHex = tabT (unpack 6156 13 (CertificateChecks.KernelCensus.J3S.F k)) ∧
      canonK 6156 13 (mask 13) (6156 * 13) (CertificateChecks.KernelCensus.J3S.F k) = true := by
  refine ⟨?_, (jiv_spec (base_parts.2.1 k hk)).1⟩
  rw [← gen_nat hk, tabT_natArr]

theorem genTbls_eq : j3GenTbls = [hexT 4 6156 (6156 * 0) j3StrongHex,
    hexT 4 6156 (6156 * 1) j3StrongHex] := rfl

theorem strong_eq {k : Nat} (hk : k < 2) :
    j3StrongArrs[k]! = unpack 6156 13 (CertificateChecks.KernelCensus.J3S.F k) := by
  have e : j3StrongArrs[k]! = CFSG.Monster.B.Co2.Native.hexTable 4 6156 (6156 * k) j3StrongHex := by
    rw [j3StrongArrs, getElem!_pos _ k (by simpa using Nat.lt_of_lt_of_le hk (by decide : 2 ≤ 5)),
      Array.getElem_ofFn]
  rw [e, CertificateChecks.KernelCensus.J3S.eq]
  exact CFSG.KC.Misc.HexFlat.hexTable_sound CertificateChecks.KernelCensus.J3S.all k
    (Nat.lt_of_lt_of_le hk (by decide))

theorem letter_tab {l : Nat} (hl : 1 ≤ l ∧ l ≤ 2) :
    j3GenTbls.getD (l - 1) (idT 6156) = tabT (unpack 6156 13 (jA l)) ∧
      canonK 6156 13 (mask 13) (6156 * 13) (jA l) = true := by
  obtain ⟨h1, h2⟩ := hl
  rcases (by omega : l = 1 ∨ l = 2) with rfl | rfl
  · have e1 : j3GenTbls.getD (1 - 1) (idT 6156) = hexT 4 6156 (6156 * 0) j3StrongHex := by
      rw [genTbls_eq, Nat.sub_self, List.getD_cons_zero]
    have e2 : jA 1 = CertificateChecks.KernelCensus.J3S.F 0 := by unfold jA; rfl
    rw [e1, e2]
    exact gen_tab (k := 0) (by norm_num)
  · have e1 : j3GenTbls.getD (2 - 1) (idT 6156) = hexT 4 6156 (6156 * 1) j3StrongHex := by
      rw [genTbls_eq, (by rfl : (2 : Nat) - 1 = 0 + 1), List.getD_cons_succ, List.getD_cons_zero]
    have e2 : jA 2 = CertificateChecks.KernelCensus.J3S.F 1 := by unfold jA; rfl
    rw [e1, e2]
    exact gen_tab (k := 1) (by norm_num)

theorem word_ok {wd : List Nat} (hl : (wd.all fun l => decide (1 ≤ l ∧ l ≤ 2)) = true) {k : Nat}
    (hk : k < 8) (h : Nat.beq (jW wd) (SY.F k) = true) :
    ((wd.all fun l => decide (1 ≤ l ∧ l ≤ 2)) && permOK 6156 (j3SylTbl k) &&
      tblEq 6156 (wordTbl 6156 j3GenTbls wd) (j3SylTbl k)) = true := by
  have hl' : ∀ l ∈ wd, 1 ≤ l ∧ l ≤ 2 := fun l hm => by
    have := List.all_eq_true.1 hl l hm
    simpa using this
  obtain ⟨e, c⟩ := wordTbl_unpack hid hidc (S := jA) fun l hm => letter_tab (hl' l hm)
  rw [hl, sy_inv hk, e, (sy_tab hk).1, tblEq_unpack c (sy_tab hk).2]
  exact h

theorem SE_G : ∀ j < 2, SE.G j = pidn 6156 13 := fun j hj => ((base_parts.2.2.2.2.2.1) j hj).2.1

theorem SE_tabs : TabsOK 6156 13 2 SE.GI j3SylGens.toArray := by
  refine ⟨rfl, fun j hj => ?_⟩
  rw [getElem!_pos _ j (by simpa [j3SylGens] using hj), List.getElem_toArray,
    ((base_parts.2.2.2.2.2.1) j hj).1]
  have e : j3SylGens[j]'(by simpa [j3SylGens] using hj) = j3SylTbl j := by
    interval_cases j <;> rfl
  rw [e]
  exact sy_tab (by omega)

theorem SE_inv : ∀ j < 2, invEqK 6156 13 (mask 13) (6156 * 13) (SE.GI j) (SEI j) = true ∧
    canonK 6156 13 (mask 13) (6156 * 13) (SEI j) = true := fun j hj =>
  ⟨(jiv_spec ((base_parts.2.2.2.2.2.1) j hj).2.2).2.2,
    (jiv_spec ((base_parts.2.2.2.2.2.1) j hj).2.2).2.1⟩

theorem pb_all : ∀ k < 16, c131001Pb k = true := by
  intro k hk
  interval_cases k
  exacts [c131001Pb0, c131001Pb1, c131001Pb2, c131001Pb3, c131001Pb4, c131001Pb5, c131001Pb6,
    c131001Pb7, c131001Pb8, c131001Pb9, c131001Pb10, c131001Pb11, c131001Pb12, c131001Pb13,
    c131001Pb14, c131001Pb15]

theorem hv_all : ∀ k < 16, c131001Hu k = true := by
  intro k hk
  interval_cases k
  exacts [c131001Hu0, c131001Hu1, c131001Hu2, c131001Hu3, c131001Hu4, c131001Hu5, c131001Hu6,
    c131001Hu7, c131001Hu8, c131001Hu9, c131001Hu10, c131001Hu11, c131001Hu12, c131001Hu13,
    c131001Hu14, c131001Hu15]

theorem fp_all : ∀ k < 4, c131001Fp k = true := by
  intro k hk
  interval_cases k
  exacts [c131001Fp0, c131001Fp1, c131001Fp2, c131001Fp3]

theorem gen_w0 : wordEqK 6156 13 (mask 13) (pidn 6156 13) CertificateChecks.KernelSporSch.PJ3.S
    CertificateChecks.KernelSporSch.PJ3.SI 5 [(1 : Int)] (CertificateChecks.KernelCensus.J3S.F 0) =
      true := by
  quickRfl

theorem gen_w1 : wordEqK 6156 13 (mask 13) (pidn 6156 13) CertificateChecks.KernelSporSch.PJ3.S
    CertificateChecks.KernelSporSch.PJ3.SI 5 [(2 : Int)] (CertificateChecks.KernelCensus.J3S.F 1) =
      true := by
  quickRfl

theorem mj_letter {l : Nat} (hl : 1 ≤ l ∧ l ≤ 2) : CertificateChecks.KernelJ3Ref.MJ (jA l) := by
  obtain ⟨h1, h2⟩ := hl
  rcases (by omega : l = 1 ∨ l = 2) with rfl | rfl
  · have e : jA 1 = CertificateChecks.KernelCensus.J3S.F 0 := by unfold jA; rfl
    rw [e]
    exact CertificateChecks.KernelJ3Ref.mj_of_word (gen_tab (k := 0) (by norm_num)).2 gen_w0
  · have e : jA 2 = CertificateChecks.KernelCensus.J3S.F 1 := by unfold jA; rfl
    rw [e]
    exact CertificateChecks.KernelJ3Ref.mj_of_word (gen_tab (k := 1) (by norm_num)).2 gen_w1

theorem mj_wfold : ∀ (wd : List Nat) (acc : Nat), CertificateChecks.KernelJ3Ref.MJ acc →
    (∀ l ∈ wd, 1 ≤ l ∧ l ≤ 2) →
      CertificateChecks.KernelJ3Ref.MJ (wfoldK 6156 13 (mask 13) jA wd acc)
  | [], _, h, _ => h
  | l :: wd, acc, h, hl => by
    have e : wfoldK 6156 13 (mask 13) jA (l :: wd) acc =
        wfoldK 6156 13 (mask 13) jA wd (pcomp 6156 13 (mask 13) acc (jA l)) := by
      change strictN (pcomp 6156 13 (mask 13) acc (jA l)) (fun a => wfoldK 6156 13 (mask 13) jA wd a) = _
      rw [CFSG.KS.Raw.Orb.strictN_eq]
    rw [e]
    exact mj_wfold wd _ (CertificateChecks.KernelJ3Ref.mj_faith.comp _ _ h
      (mj_letter (hl l List.mem_cons_self))) fun l' hm => hl l' (List.mem_cons_of_mem _ hm)

theorem sw_mj {wd : List Int} {k : Nat} (hk : k < 8)
    (h : wordEqK 6156 13 (mask 13) (pidn 6156 13) CertificateChecks.KernelSporSch.PJ3.S
      CertificateChecks.KernelSporSch.PJ3.SI 5 wd (SY.F k) = true) :
    CertificateChecks.KernelJ3Ref.MJ (SY.F k) :=
  CertificateChecks.KernelJ3Ref.mj_of_word (sy_tab hk).2 h

theorem jTr_cons (l : Nat) (wd : List Nat) (x : Nat) :
    jTr (l :: wd) x = pg 13 (mask 13) (jA l) (jTr wd x) := by
  change strictN (jTr wd x) (fun y => pg 13 (mask 13) (jA l) y) = _
  rw [CFSG.KS.Raw.Orb.strictN_eq]

theorem tr_lt : ∀ (wd : List Nat), (∀ l ∈ wd, 1 ≤ l ∧ l ≤ 2) → ∀ x < 6156, jTr wd x < 6156
  | [], _, _, hx => hx
  | l :: wd, hl, x, hx => by
    rw [jTr_cons]
    exact (PF.canon_facts (letter_tab (hl l List.mem_cons_self)).2).2.2.2 _
      (tr_lt wd (fun l' hm => hl l' (List.mem_cons_of_mem _ hm)) x hx)

theorem pg_wfold : ∀ (wd : List Nat) (acc : Nat), (∀ l ∈ wd, 1 ≤ l ∧ l ≤ 2) → ∀ x < 6156,
    pg 13 (mask 13) (wfoldK 6156 13 (mask 13) jA wd acc) x = pg 13 (mask 13) acc (jTr wd x)
  | [], _, _, _, _ => rfl
  | l :: wd, acc, hl, x, hx => by
    have e : wfoldK 6156 13 (mask 13) jA (l :: wd) acc =
        wfoldK 6156 13 (mask 13) jA wd (pcomp 6156 13 (mask 13) acc (jA l)) := by
      change strictN (pcomp 6156 13 (mask 13) acc (jA l)) (fun a => wfoldK 6156 13 (mask 13) jA wd a) = _
      rw [CFSG.KS.Raw.Orb.strictN_eq]
    have hl' : ∀ l' ∈ wd, 1 ≤ l' ∧ l' ≤ 2 := fun l' hm => hl l' (List.mem_cons_of_mem _ hm)
    rw [e, pg_wfold wd _ hl' x hx, PF.pg_pcomp (by norm_num) (tr_lt wd hl' x hx), jTr_cons]

theorem wbL_spec (wd : List Nat) (P : Nat) : ∀ L : List Nat, jWBL wd P L = true →
    ∀ b ∈ L, jTr wd b = pg 13 (mask 13) P b
  | [], _ => fun _ hb => absurd hb List.not_mem_nil
  | b :: L, h => by
    have h' : (Nat.beq (jTr wd b) (pg 13 (mask 13) P b) && jWBL wd P L) = true := by
      rw [← CFSG.KS.Raw.Orb.bAnd_eq]
      exact h
    rw [Bool.and_eq_true] at h'
    rw [List.forall_mem_cons]
    exact ⟨Nat.eq_of_beq_eq_true h'.1, wbL_spec wd P L h'.2⟩

theorem word_eq {wd : List Nat} (hl : (wd.all fun l => decide (1 ≤ l ∧ l ≤ 2)) = true) {k : Nat}
    (hM : CertificateChecks.KernelJ3Ref.MJ (SY.F k)) (h : jWB wd (SY.F k) = true) :
    Nat.beq (jW wd) (SY.F k) = true := by
  have hl' : ∀ l ∈ wd, 1 ≤ l ∧ l ≤ 2 := fun l hm => by
    have := List.all_eq_true.1 hl l hm
    simpa using this
  have hW : CertificateChecks.KernelJ3Ref.MJ (jW wd) :=
    mj_wfold wd _ CertificateChecks.KernelJ3Ref.mj_faith.id hl'
  have e := CertificateChecks.KernelJ3Ref.mj_faith.eq _ _ hW hM fun b hb => by
    have hb6 : b < 6156 := CertificateChecks.KernelJ3Ref.mj_faith.bs_lt b hb
    rw [jW, pg_wfold wd _ hl' b hb6, jid, PF.pg_pidn (by norm_num) (by norm_num) (tr_lt wd hl' b hb6)]
    exact wbL_spec wd _ bsC h b hb
  rw [e]
  exact Nat.beq_refl _

theorem hGI : ∀ j < 2, CertificateChecks.KernelJ3Ref.MJ (SE.GI j) := by
  intro j hj
  rw [((base_parts.2.2.2.2.2.1) j hj).1]
  rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
  · exact sw_mj (by norm_num) c131001_sw0
  · exact sw_mj (by norm_num) c131001_sw1

theorem hGJ : ∀ j < 2, CertificateChecks.KernelJ3Ref.MJ (SEI j) := fun j hj =>
  CertificateChecks.KernelJ3Ref.mj_inv (hGI j hj) (SE_inv j hj).2 (SE_inv j hj).1

theorem hHd : penumHdK (pidn 6156 13) SE.cnt 300 SE.T SE.PL = true := base_parts.2.2.2.2.1

theorem sPb : ∀ i < SE.cnt, penumPtB 6156 13 (mask 13) CertificateChecks.KernelJ3Ref.bsJ SE.GI 2
    SE.cnt SE.T SE.PL SE.POS SE.SRT SE.SRI i = true := by
  intro i hi
  have hc := hcnt
  have hk : i / 16 < 16 := by omega
  exact slK_spec (pb_all (i / 16) hk) i (by change 16 * (i / 16) ≤ i; omega)
    (by change i < 16 * (i / 16) + 16; omega) hi

theorem hTJ : ∀ i < SE.cnt, CertificateChecks.KernelJ3Ref.MJ (SE.T i) :=
  penumB_mem CertificateChecks.KernelJ3Ref.mj_faith hGI hHd sPb

theorem cay_all : ∀ k < 15, c131001Cay k = true := by
  intro k hk
  interval_cases k
  exacts [c131001Cay0, c131001Cay1, c131001Cay2, c131001Cay3, c131001Cay4, c131001Cay5,
    c131001Cay6, c131001Cay7, c131001Cay8, c131001Cay9, c131001Cay10, c131001Cay11, c131001Cay12,
    c131001Cay13, c131001Cay14]

theorem el_all : ∀ k < 16, c131001El k = true := by
  intro k hk
  interval_cases k
  exacts [c131001El0, c131001El1, c131001El2, c131001El3, c131001El4, c131001El5, c131001El6,
    c131001El7, c131001El8, c131001El9, c131001El10, c131001El11, c131001El12, c131001El13,
    c131001El14, c131001El15]

theorem sPe : ∀ i < SE.cnt, penumPtK 6156 13 (mask 13) (6156 * 13) true SE.G SE.GI 2 SE.cnt SE.T
    SE.PL SE.POS SE.SRT SE.SRI i = true :=
  penumPtK_of_B CertificateChecks.KernelJ3Ref.mj_faith hGI SE_G hHd sPb

theorem sHs : ∀ i < SE.cnt, hsortPtK 6156 13 (mask 13) SE.cnt SE.T SE.HS SE.HSI i = true := by
  have hc := hcnt
  refine hsortPtK_of_V (HV := SEV) (fun i hi => ?_) (fun i hi => ?_)
  · have hk : i / 16 < 16 := by omega
    have h := slK_spec (hv_all (i / 16) hk) i (by change 16 * (i / 16) ≤ i; omega)
      (by change i < 16 * (i / 16) + 16; omega) hi
    unfold jHu at h
    unfold hvK
    rw [← hkeyU_eq]
    exact h
  · exact slK_spec c131001_hsv i (by change 0 ≤ i; omega) (by change i < 0 + 256; omega) hi

theorem sCl : ∀ c < SE.cnt * (2 + 2), findPtK SE.cnt SE.T
    (prodQK 6156 13 (mask 13) (2 + 2) SE.T (bothK 2 SE.GI SEI)) SECl c = true := by
  intro c hc'
  have hc := hcnt
  have hk : c / 256 < 4 := by omega
  have hS : ∀ j < 2 + 2, CertificateChecks.KernelJ3Ref.MJ (bothK 2 SE.GI SEI j) := fun j hj => by
    rcases Nat.lt_or_ge j 2 with h | h
    · rw [bothK_lt h]
      exact hGI j h
    · rw [bothK_ge h]
      exact hGJ _ (by omega)
  exact findPtK_prod_of_B CertificateChecks.KernelJ3Ref.mj_faith hTJ hS hc'
    (slK_spec (fp_all (c / 256) hk) c (by change 256 * (c / 256) ≤ c; omega)
      (by change c < 256 * (c / 256) + 256; omega) (by change c < SE.cnt * 4; omega))

theorem sCay : ∀ c < SE.cnt * SE.cnt, cayPtK SE.cnt 2 SE.PL SE.POS SEM c = true := by
  intro c hc'
  rw [hcnt] at hc' ⊢
  have hk : c / 4096 < 15 := by omega
  exact slK_spec (cay_all (c / 4096) hk) c (by change 4096 * (c / 4096) ≤ c; omega)
    (by change c < 4096 * (c / 4096) + 4096; omega) (by change c < 243 * 243; omega)

theorem sEl : ∀ i < 243, jEl i = true := by
  intro i hi
  have hk : i / 16 < 16 := by omega
  exact slK_spec (el_all (i / 16) hk) i (by change 16 * (i / 16) ≤ i; omega)
    (by change i < 16 * (i / 16) + 16; omega) hi

theorem hT : ∀ q < SE.cnt, canonK 6156 13 (mask 13) (6156 * 13) (SE.T q) = true :=
  fun q hq => penumPt_canon (sPe q hq)

theorem hT0 : SE.T 0 = pidn 6156 13 := by
  have h := base_parts.2.2.2.2.1
  unfold penumHdK at h
  simp only [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
  exact Nat.eq_of_beq_eq_true h.2.2.1

theorem T_inj {a b : Nat} (ha : a < 243) (hb : b < 243) : Nat.beq (SE.T a) (SE.T b) = Nat.beq a b := by
  have hS : ∀ i < SE.cnt, r32 SE.SRT i < SE.cnt ∧ r32 SE.SRI (r32 SE.SRT i) = i ∧
      (i + 1 < SE.cnt → SE.T (r32 SE.SRT i) < SE.T (r32 SE.SRT (i + 1))) :=
    fun i hi => (penumPt_specH (sPe i hi)).2.2.2
  have hinj := inj_of_sortH hS
  rw [hcnt] at hinj
  cases e : Nat.beq a b
  · cases e' : Nat.beq (SE.T a) (SE.T b)
    · rfl
    · exact absurd (hinj a ha b hb (Nat.eq_of_beq_eq_true e')) (Nat.ne_of_beq_eq_false e)
  · rw [Nat.eq_of_beq_eq_true e]
    exact Nat.beq_refl _

theorem prod_eq {a b : Nat} (ha : a < 243) (hb : b < 243) :
    jq a b < 243 ∧ pcomp 6156 13 (mask 13) (SE.T a) (SE.T b) = SE.T (jq a b) := by
  have h := cay_sound SE_G (fun j hj => (SE_tabs.2 j hj).2) hT0 sPe sCay a (by rw [hcnt]; exact ha)
    b (by rw [hcnt]; exact hb)
  rw [hcnt] at h
  exact h

theorem powT_unpack {p : Nat} (hp : canonK 6156 13 (mask 13) (6156 * 13) p = true) :
    ∀ e, powT 6156 e (tabT (unpack 6156 13 p)) = tabT (unpack 6156 13 (powPK 6156 13 (mask 13) p e)) ∧
      canonK 6156 13 (mask 13) (6156 * 13) (powPK 6156 13 (mask 13) p e) = true
  | 0 => ⟨hid, hidc⟩
  | e + 1 => by
    obtain ⟨h1, h2⟩ := powT_unpack hp e
    have e1 : powT 6156 (e + 1) (tabT (unpack 6156 13 p)) =
        compT 6156 (tabT (unpack 6156 13 p)) (powT 6156 e (tabT (unpack 6156 13 p))) := rfl
    rw [e1, h1, compT_unpack hp h2, powPK_succ]
    exact ⟨rfl, CFSG.KC.BfsPin.canonK_pcomp hp h2⟩

theorem not_bIf (c : Bool) : bIf(c, false, true) = !c := by cases c <;> rfl

theorem wit_ok {kx ka kb : Nat} (hx : kx < 8) (ha : ka < 8) (hb : kb < 8)
    (h : jWit (SY.F kx) (SY.F ka) (SY.F kb) = true) :
    wit235OK 6156 ⟨j3SylTbl kx, j3SylTbl ka, j3SylTbl kb⟩ = true := by
  obtain ⟨ex, cx⟩ := sy_tab hx
  obtain ⟨ea, ca⟩ := sy_tab ha
  obtain ⟨eb, cb⟩ := sy_tab hb
  unfold wit235OK
  simp only []
  rw [sy_inv hx, sy_inv ha, sy_inv hb, ex, ea, eb, commTT_unpack ca cx, commTT_unpack cb cx,
    (powT_unpack ca 2).1, (powT_unpack cb 3).1, compT_unpack ca cb,
    (powT_unpack (CFSG.KC.BfsPin.canonK_pcomp ca cb) 5).1, hid,
    tblEq_unpack (powT_unpack ca 2).2 hidc, tblEq_unpack (powT_unpack cb 3).2 hidc,
    tblEq_unpack (powT_unpack (CFSG.KC.BfsPin.canonK_pcomp ca cb) 5).2 hidc,
    tblEq_unpack ca hidc, tblEq_unpack cb hidc]
  unfold jWit at h
  rw [not_bIf, not_bIf] at h
  simp only [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  simp only [jc, jid] at h1 h2 h3 h4 h5 h6 h7
  rw [h1, h2, h3, h4, h5, h6, h7]
  rfl

theorem cntBelow_eq (q : Nat → Bool) : cntBelowK 243 q 4 = (List.range 243).countP q := by
  unfold cntBelowK
  rw [CFSG.KS.PEnum.cntK_eq, countP_range_lt q (by norm_num)]

theorem el_ok {i : Nat} (hi : i < 243) :
    (!(selOK 6156 [3] (tabT (unpack 6156 13 (SE.T i)))) ||
      ((hRec 6156 13 SE.cnt SE.T SE.PL).1.toList.countP fun y =>
        commTT 6156 y (tabT (unpack 6156 13 (SE.T i)))) % 81 == 0 ||
      j3Wits.any fun w => (hRec 6156 13 SE.cnt SE.T SE.PL).1.toList.any fun p =>
        tblEq 6156 (compT 6156 p w.x) (compT 6156 (tabT (unpack 6156 13 (SE.T i))) p)) = true := by
  have hTi := hT i (by rw [hcnt]; exact hi)
  have hT' : ∀ q < 243, canonK 6156 13 (mask 13) (6156 * 13) (SE.T q) = true :=
    fun q hq => hT q (by rw [hcnt]; exact hq)
  have hbeqT : ∀ a < 243, ∀ b < 243, tblEq 6156 (tabT (unpack 6156 13 (SE.T a)))
      (tabT (unpack 6156 13 (SE.T b))) = Nat.beq a b := fun a ha b hb => by
    rw [tblEq_unpack (hT' a ha) (hT' b hb), T_inj ha hb]
  have hpr : ∀ a < 243, ∀ b < 243, compT 6156 (tabT (unpack 6156 13 (SE.T a)))
      (tabT (unpack 6156 13 (SE.T b))) = tabT (unpack 6156 13 (SE.T (jq a b))) ∧ jq a b < 243 :=
    fun a ha b hb => by
      rw [compT_unpack (hT' a ha) (hT' b hb), (prod_eq ha hb).2]
      exact ⟨rfl, (prod_eq ha hb).1⟩
  have hsel : selOK 6156 [3] (tabT (unpack 6156 13 (SE.T i))) =
      (!Nat.beq i 0 && Nat.beq (jq i (jq i i)) 0) := by
    have hp3 : powT 6156 3 (tabT (unpack 6156 13 (SE.T i))) =
        tabT (unpack 6156 13 (SE.T (jq i (jq i i)))) := by
      have e1 : powT 6156 3 (tabT (unpack 6156 13 (SE.T i))) = compT 6156 (tabT (unpack 6156 13 (SE.T i)))
          (compT 6156 (tabT (unpack 6156 13 (SE.T i))) (compT 6156 (tabT (unpack 6156 13 (SE.T i)))
            (idT 6156))) := rfl
      have e2 : compT 6156 (tabT (unpack 6156 13 (SE.T i))) (idT 6156) =
          tabT (unpack 6156 13 (SE.T i)) := by
        rw [hid, compT_unpack hTi hidc, (pcomp_id_c hTi).1]
      obtain ⟨p1, q1⟩ := hpr i hi i hi
      obtain ⟨p2, -⟩ := hpr i hi _ q1
      rw [e1, e2, p1, p2]
    unfold selOK
    simp only [List.any_cons, List.any_nil, Bool.or_false]
    have hidT : idT 6156 = tabT (unpack 6156 13 (SE.T 0)) := by rw [hT0, hid]
    have hq := (prod_eq hi (prod_eq hi hi).1).1
    rw [hp3, hidT, hbeqT i hi 0 (by norm_num), hbeqT _ hq 0 (by norm_num)]
  have hcount : ((hRec 6156 13 SE.cnt SE.T SE.PL).1.toList.countP fun y =>
      commTT 6156 y (tabT (unpack 6156 13 (SE.T i)))) =
      cntBelowK 243 (fun j => Nat.beq (jq j i) (jq i j)) 4 := by
    rw [hcnt]
    refine countP_hRec (by norm_num) fun j hj => ?_
    rw [commTT_unpack (hT' j hj) hTi, (prod_eq hj hi).2, (prod_eq hi hj).2, T_inj (prod_eq hj hi).1
      (prod_eq hi hj).1]
  have hwit : (∃ p < 243, (bIf(Nat.beq (jq p (r32 SEX 0)) (jq i p), true,
      Nat.beq (jq p (r32 SEX 1)) (jq i p))) = true) →
      (j3Wits.any fun w => (hRec 6156 13 SE.cnt SE.T SE.PL).1.toList.any fun p =>
        tblEq 6156 (compT 6156 p w.x) (compT 6156 (tabT (unpack 6156 13 (SE.T i))) p)) = true := by
    rintro ⟨p, hp, hpq⟩
    obtain ⟨x0, ex0⟩ := base_parts.2.2.2.2.2.2 0 (by norm_num)
    obtain ⟨x1, ex1⟩ := base_parts.2.2.2.2.2.2 1 (by norm_num)
    rw [hcnt] at x0 x1
    have tx0 : j3SylTbl 2 = tabT (unpack 6156 13 (SE.T (r32 SEX 0))) := by
      rw [ex0]; exact (sy_tab (by norm_num)).1
    have tx1 : j3SylTbl 5 = tabT (unpack 6156 13 (SE.T (r32 SEX 1))) := by
      rw [ex1]; exact (sy_tab (by norm_num)).1
    have hmem : tabT (unpack 6156 13 (SE.T p)) ∈ (hRec 6156 13 SE.cnt SE.T SE.PL).1.toList := by
      simp only [hRec, Array.toList_ofFn, List.mem_ofFn]
      exact ⟨⟨p, by rw [hcnt]; exact hp⟩, rfl⟩
    have hany : ∀ (r : Nat), r < 243 → Nat.beq (jq p r) (jq i p) = true →
        ((hRec 6156 13 SE.cnt SE.T SE.PL).1.toList.any fun q =>
          tblEq 6156 (compT 6156 q (tabT (unpack 6156 13 (SE.T r))))
            (compT 6156 (tabT (unpack 6156 13 (SE.T i))) q)) = true := by
      intro r hr hb
      rw [List.any_eq_true]
      refine ⟨_, hmem, ?_⟩
      rw [(hpr p hp r hr).1, (hpr i hi p hp).1, hbeqT _ (hpr p hp r hr).2 _ (hpr i hi p hp).2]
      exact hb
    unfold j3Wits
    simp only [List.any_cons, List.any_nil, Bool.or_false]
    rw [tx0, tx1]
    rw [CFSG.KS.Raw.Orb.bIf_eq] at hpq
    split_ifs at hpq with hh
    · rw [hany _ x0 hh]
      rfl
    · rw [hany _ x1 hpq, Bool.or_true]
  have hel := sEl i hi
  unfold jEl at hel
  simp only [CFSG.KS.Raw.Orb.bIf_eq] at hel
  rw [hsel, hcount]
  cases h0 : Nat.beq i 0
  · rw [h0, if_neg Bool.false_ne_true] at hel
    cases h3 : Nat.beq (jq i (jq i i)) 0
    · rfl
    · rw [h3, if_pos rfl] at hel
      simp only [Bool.not_false, Bool.true_and, Bool.not_true, Bool.false_or, Bool.or_eq_true,
        beq_iff_eq]
      by_cases h81 : Nat.beq (Nat.mod (cntBelowK 243 (fun j => Nat.beq (jq j i) (jq i j)) 4) 81) 0 = true
      · exact Or.inl (Nat.eq_of_beq_eq_true h81)
      · rw [if_neg h81] at hel
        have hpos := Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_ble_eq_true hel)
        rw [cntBelow_eq] at hpos
        obtain ⟨p, hpm, hpq⟩ := List.countP_pos_iff.1 hpos
        exact Or.inr (hwit ⟨p, List.mem_range.1 hpm, by rw [CFSG.KS.Raw.Orb.bIf_eq]; exact hpq⟩)
  · rfl

theorem j3SylOK_true : j3SylOK = true := by
  have he := enumOK_of hnJ SE_G SE_tabs SE_inv base_parts.2.2.2.2.1 sPe sHs sCl hcnt
  have hmul := mulH_sound hnJ SE_G SE_tabs base_parts.2.2.2.2.1 sPe sHs
  have h1 : j3GenTbls.all (fun g => permOK 6156 g) = true := by
    rw [genTbls_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_true]
    rw [(gen_tab (k := 0) (by norm_num)).1, (gen_tab (k := 1) (by norm_num)).1,
      permOK_unpack (gen_tab (k := 0) (by norm_num)).2 (jiv_spec (base_parts.2.1 0 (by norm_num))).2.2,
      permOK_unpack (gen_tab (k := 1) (by norm_num)).2 (jiv_spec (base_parts.2.1 1 (by norm_num))).2.2]
    rfl
  have h2 : (j3GenTbls.map natArr == [j3StrongArrs[0]!, j3StrongArrs[1]!]) = true := by
    rw [genTbls_eq]
    simp only [List.map_cons, List.map_nil]
    rw [gen_nat (k := 0) (by norm_num), gen_nat (k := 1) (by norm_num),
      strong_eq (k := 0) (by norm_num), strong_eq (k := 1) (by norm_num)]
    exact beq_self_eq_true _
  have h3 : j3WordPairs.all (fun p => p.1.all (fun l => decide (1 ≤ l ∧ l ≤ 2)) &&
      permOK 6156 p.2 && tblEq 6156 (wordTbl 6156 j3GenTbls p.1) p.2) = true := by
    unfold j3WordPairs
    simp only [List.all_cons, List.all_nil, Bool.and_true]
    rw [word_ok (by decide) (by norm_num) (word_eq (by decide) (sw_mj (by norm_num) c131001_sw0)
        c131001_wb0),
      word_ok (by decide) (by norm_num) (word_eq (by decide) (sw_mj (by norm_num) c131001_sw1)
        c131001_wb1),
      word_ok (by decide) (by norm_num) (word_eq (by decide) (sw_mj (by norm_num) c131001_sw2)
        c131001_wb2),
      word_ok (by decide) (by norm_num) (word_eq (by decide) (sw_mj (by norm_num) c131001_sw3)
        c131001_wb3),
      word_ok (by decide) (by norm_num) (word_eq (by decide) (sw_mj (by norm_num) c131001_sw4)
        c131001_wb4),
      word_ok (by decide) (by norm_num) (word_eq (by decide) (sw_mj (by norm_num) c131001_sw5)
        c131001_wb5)]
    rfl
  have h4 : j3SylGens.all (fun g => permOK 6156 g) = true := by
    unfold j3SylGens
    simp only [List.all_cons, List.all_nil, Bool.and_true]
    rw [sy_inv (by norm_num), sy_inv (by norm_num)]
    rfl
  have h5 : j3Wits.all (wit235OK 6156) = true := by
    have h0 := c131001_wit
    unfold c131001Wit at h0
    simp only [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h0
    obtain ⟨w1, w2⟩ := h0
    unfold j3Wits
    simp only [List.all_cons, List.all_nil, Bool.and_true]
    rw [wit_ok (by norm_num) (by norm_num) (by norm_num) w1,
      wit_ok (by norm_num) (by norm_num) (by norm_num) w2]
    rfl
  have h6 : ((mulClosureH 6156 j3SylGens.toArray 300).1.toList.all fun s =>
      !(selOK 6156 [3] s) || ((mulClosureH 6156 j3SylGens.toArray 300).1.toList.countP fun y =>
        commTT 6156 y s) % 81 == 0 ||
      j3Wits.any fun w => (mulClosureH 6156 j3SylGens.toArray 300).1.toList.any fun p =>
        tblEq 6156 (compT 6156 p w.x) (compT 6156 s p)) = true := by
    rw [hmul.1, List.all_eq_true]
    intro s hs
    simp only [hRec, Array.toList_ofFn, List.mem_ofFn] at hs
    obtain ⟨⟨i, hi⟩, rfl⟩ := hs
    have hi' : i < 243 := by rw [← hcnt]; exact hi
    have := el_ok hi'
    simp only [hRec, Array.toList_ofFn] at this
    exact this
  unfold j3SylOK sylowCentWitOK
  simp only []
  rw [h1, h2, h3, h4, he, h5, h6]
  rfl

end CFSG.KD.E27J3S

end
