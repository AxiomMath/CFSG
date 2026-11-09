module

public import Certificates.Kernel.CoreD2K.RuFive.Data
public import Certificates.Kernel.CoreD2K.RuFive.SLPData
public import Certificates.Data.Kernel.CoreD2K.Check
public import Certificates.Data.Kernel.Spor.PEnum
public import Certificates.Data.Kernel.CoreD2K.Extra
public import Certificates.Data.CoreD2LinesOne
public import CFSG.Certificates.Kernel.PermSLPSound
public import CFSG.Certificates.Kernel.Spor.PK.Basic
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallChunks
import Certificates.Kernel.Sporadic.ON.Gen

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelCoreD2K.RuFive

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.CoreD2K
open CFSG.KC.PermSLP
open Certificates.CoreD2Perm

@[expose] noncomputable def cnR (p : Nat) : Bool := canonK 4060 12 (mask 12) (4060 * 12) p

@[expose] noncomputable def rA (k : Nat) : Bool := ruleK 4060 12 4 GP GPI PAV PAG k

@[expose] noncomputable def rB (k : Nat) : Bool := ruleK 4060 12 16 GT GTI PBV PBG k

@[expose] noncomputable def rfLn (i : Nat) : Bool :=
  allN 6 (fun j => bIf(Nat.blt i j, strictB (RE.G (V.ys.getD j (nat_lit 0))) (fun x =>
    outK 4060 12 5 (RE.G (nat_lit 0)) (RE.G (V.ys.getD i (nat_lit 0))) x), true))

end CertificateChecks.KernelCoreD2K.RuFive

#kon_slices CertificateChecks.KernelCoreD2K.RuFive.rA 0 427
#kon_join CertificateChecks.KernelCoreD2K.RuFive.rAll CertificateChecks.KernelCoreD2K.RuFive.rA 427
#kon_slices CertificateChecks.KernelCoreD2K.RuFive.rB 0 439
#kon_join CertificateChecks.KernelCoreD2K.RuFive.rBll CertificateChecks.KernelCoreD2K.RuFive.rB 439
#kon_slices CertificateChecks.KernelCoreD2K.RuFive.rfLn 0 6
#kon_join CertificateChecks.KernelCoreD2K.RuFive.rfLnAll CertificateChecks.KernelCoreD2K.RuFive.rfLn 6

namespace CertificateChecks.KernelCoreD2K.RuFive

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.CoreD2K
open CFSG.KC.PermSLP
open Certificates.CoreD2Perm

theorem k_sz : szOK 4060 12 = true := by quickRfl
theorem k_gp : allN (nat_lit 2) (fun j => permOK 4060 12 (mask 12) (Nat.mul 4060 12) (GP j) (GPI j)) =
    true := by quickRfl

theorem kCnP : (cnR (GP 0) && cnR (GP 1) && cnR (GPI 0) && cnR (GPI 1) && cnR (pidn 4060 12)) =
    true := by quickRfl
theorem kCnT : allN 8 (fun j => cnR (GT j) && cnR (GTI j)) = true := by quickRfl

theorem kLA : allN 4 (fun s => letK 4060 12 4 GP GPI PAV s) = true := by quickRfl
theorem kLB : allN 16 (fun s => letK 4060 12 16 GT GTI PBV s) = true := by quickRfl

theorem gp_mod (j : Nat) : GP j = GP (j % 2) ∧ GPI j = GPI (j % 2) := by
  have h : Nat.land j (nat_lit 1) = Nat.land (j % 2) (nat_lit 1) := by
    change j &&& 1 = (j % 2) &&& 1
    rw [Nat.and_one_is_mod, Nat.and_one_is_mod, Nat.mod_mod]
  delta GP GPI
  beta_reduce
  rw [h]
  exact ⟨rfl, rfl⟩

theorem gt_mod (j : Nat) : GT j = GT (j % 8) ∧ GTI j = GTI (j % 8) := by
  have h : Nat.land j (nat_lit 7) = Nat.land (j % 8) (nat_lit 7) := by
    have e7 : (7 : Nat) = 2 ^ 3 - 1 := rfl
    change j &&& 7 = (j % 8) &&& 7
    rw [e7, Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod]
    omega
  delta GT GTI
  beta_reduce
  rw [h]
  exact ⟨rfl, rfl⟩

theorem cnGP : ∀ j, cnR (GP j) = true ∧ cnR (GPI j) = true := by
  have h := kCnP
  simp only [Bool.and_eq_true] at h
  intro j
  rw [(gp_mod j).1, (gp_mod j).2]
  have hb : j % 2 < 2 := Nat.mod_lt _ (by omega)
  generalize j % 2 = k at hb ⊢
  match k, hb with
  | 0, _ => exact ⟨h.1.1.1.1, h.1.1.2⟩
  | 1, _ => exact ⟨h.1.1.1.2, h.1.2⟩
  | _ + 2, hb => omega

theorem cnGT : ∀ j, cnR (GT j) = true ∧ cnR (GTI j) = true := by
  have h : ∀ i < 8, cnR (GT i) = true ∧ cnR (GTI i) = true := fun i hi => by
    have := CFSG.KS.PK.allN_iff.1 kCnT i hi
    simpa only [Bool.and_eq_true] using this
  intro j
  rw [(gt_mod j).1, (gt_mod j).2]
  exact h _ (Nat.mod_lt _ (by omega))

theorem cnId : cnR (pidn 4060 12) = true := by
  have h := kCnP
  simp only [Bool.and_eq_true] at h
  exact h.2

theorem eA {kS t : Nat} {wd : List Int} {r : Nat} {c : Bool}
    (h : (lettersK kS wd && topK 4 427 431 PAG t wd && Nat.beq (symV 4 GP GPI PAV t) r && c) =
      true) :
    bAnd(wordEqK 4060 12 (mask 12) (pidn 4060 12) GP GPI kS wd r, c) = true := by
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hl, ht⟩, hv⟩, hc⟩ := h
  have hw := slp_word (n := 4060) (w := 12) (fun j => (cnGP j).1) (fun j => (cnGP j).2) cnId
    (CFSG.KS.PK.allN_iff.1 kLA) rAll (by norm_num) ht
  unfold wordEqK
  rw [k_sz, hl, hw, Nat.eq_of_beq_eq_true hv, Nat.beq_refl, hc]

theorem eB {kS t : Nat} {wd : List Int} {r : Nat}
    (h : (lettersK kS wd && topK 16 439 455 PBG t wd && Nat.beq (symV 16 GT GTI PBV t) r) =
      true) :
    wordEqK 4060 12 (mask 12) (pidn 4060 12) GT GTI kS wd r = true := by
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hl, ht⟩, hv⟩ := h
  have hw := slp_word (n := 4060) (w := 12) (fun j => (cnGT j).1) (fun j => (cnGT j).2) cnId
    (CFSG.KS.PK.allN_iff.1 kLB) rBll (by norm_num) ht
  unfold wordEqK
  rw [k_sz, hl, hw, Nat.eq_of_beq_eq_true hv, Nat.beq_refl]

theorem k_e0 : bAnd(wordEqK 4060 12 (mask 12) (pidn 4060 12) GP GPI (nat_lit 2) (V.base.eW.getD 0 [])
    (RE.G 0), canonK 4060 12 (mask 12) (Nat.mul 4060 12) (RE.G 0)) = true :=
  eA (kS := nat_lit 2) (wd := V.base.eW.getD 0 []) (r := RE.G 0)
    (c := canonK 4060 12 (mask 12) (Nat.mul 4060 12) (RE.G 0)) (t := PAT 0) (by quickRfl)
theorem k_e1 : bAnd(wordEqK 4060 12 (mask 12) (pidn 4060 12) GP GPI (nat_lit 2) (V.base.eW.getD 1 [])
    (RE.G 1), canonK 4060 12 (mask 12) (Nat.mul 4060 12) (RE.G 1)) = true :=
  eA (kS := nat_lit 2) (wd := V.base.eW.getD 1 []) (r := RE.G 1)
    (c := canonK 4060 12 (mask 12) (Nat.mul 4060 12) (RE.G 1)) (t := PAT 1) (by quickRfl)
theorem k_e2 : bAnd(wordEqK 4060 12 (mask 12) (pidn 4060 12) GP GPI (nat_lit 2) (V.base.eW.getD 2 [])
    (RE.G 2), canonK 4060 12 (mask 12) (Nat.mul 4060 12) (RE.G 2)) = true :=
  eA (kS := nat_lit 2) (wd := V.base.eW.getD 2 []) (r := RE.G 2)
    (c := canonK 4060 12 (mask 12) (Nat.mul 4060 12) (RE.G 2)) (t := PAT 2) (by quickRfl)
theorem k_e3 : bAnd(wordEqK 4060 12 (mask 12) (pidn 4060 12) GP GPI (nat_lit 2) (V.base.eW.getD 3 [])
    (RE.G 3), canonK 4060 12 (mask 12) (Nat.mul 4060 12) (RE.G 3)) = true :=
  eA (kS := nat_lit 2) (wd := V.base.eW.getD 3 []) (r := RE.G 3)
    (c := canonK 4060 12 (mask 12) (Nat.mul 4060 12) (RE.G 3)) (t := PAT 3) (by quickRfl)
theorem k_e4 : bAnd(wordEqK 4060 12 (mask 12) (pidn 4060 12) GP GPI (nat_lit 2) (V.base.eW.getD 4 [])
    (RE.G 4), canonK 4060 12 (mask 12) (Nat.mul 4060 12) (RE.G 4)) = true :=
  eA (kS := nat_lit 2) (wd := V.base.eW.getD 4 []) (r := RE.G 4)
    (c := canonK 4060 12 (mask 12) (Nat.mul 4060 12) (RE.G 4)) (t := PAT 4) (by quickRfl)
theorem k_e5 : bAnd(wordEqK 4060 12 (mask 12) (pidn 4060 12) GP GPI (nat_lit 2) (V.base.eW.getD 5 [])
    (RE.G 5), canonK 4060 12 (mask 12) (Nat.mul 4060 12) (RE.G 5)) = true :=
  eA (kS := nat_lit 2) (wd := V.base.eW.getD 5 []) (r := RE.G 5)
    (c := canonK 4060 12 (mask 12) (Nat.mul 4060 12) (RE.G 5)) (t := PAT 5) (by quickRfl)
theorem k_e6 : bAnd(wordEqK 4060 12 (mask 12) (pidn 4060 12) GP GPI (nat_lit 2) (V.base.eW.getD 6 [])
    (RE.G 6), canonK 4060 12 (mask 12) (Nat.mul 4060 12) (RE.G 6)) = true :=
  eA (kS := nat_lit 2) (wd := V.base.eW.getD 6 []) (r := RE.G 6)
    (c := canonK 4060 12 (mask 12) (Nat.mul 4060 12) (RE.G 6)) (t := PAT 6) (by quickRfl)

theorem k_g0 : bAnd(wordEqK 4060 12 (mask 12) (pidn 4060 12) GP GPI (nat_lit 2) (V.base.gWs.getD 0 [])
    (GT 0), permOK 4060 12 (mask 12) (Nat.mul 4060 12) (GT 0) (GTI 0)) = true :=
  eA (kS := nat_lit 2) (wd := V.base.gWs.getD 0 []) (r := GT 0)
    (c := permOK 4060 12 (mask 12) (Nat.mul 4060 12) (GT 0) (GTI 0)) (t := PAT 7) (by quickRfl)
theorem k_g1 : bAnd(wordEqK 4060 12 (mask 12) (pidn 4060 12) GP GPI (nat_lit 2) (V.base.gWs.getD 1 [])
    (GT 1), permOK 4060 12 (mask 12) (Nat.mul 4060 12) (GT 1) (GTI 1)) = true :=
  eA (kS := nat_lit 2) (wd := V.base.gWs.getD 1 []) (r := GT 1)
    (c := permOK 4060 12 (mask 12) (Nat.mul 4060 12) (GT 1) (GTI 1)) (t := PAT 8) (by quickRfl)
theorem k_g2 : bAnd(wordEqK 4060 12 (mask 12) (pidn 4060 12) GP GPI (nat_lit 2) (V.base.gWs.getD 2 [])
    (GT 2), permOK 4060 12 (mask 12) (Nat.mul 4060 12) (GT 2) (GTI 2)) = true :=
  eA (kS := nat_lit 2) (wd := V.base.gWs.getD 2 []) (r := GT 2)
    (c := permOK 4060 12 (mask 12) (Nat.mul 4060 12) (GT 2) (GTI 2)) (t := PAT 9) (by quickRfl)
theorem k_g3 : bAnd(wordEqK 4060 12 (mask 12) (pidn 4060 12) GP GPI (nat_lit 2) (V.base.gWs.getD 3 [])
    (GT 3), permOK 4060 12 (mask 12) (Nat.mul 4060 12) (GT 3) (GTI 3)) = true :=
  eA (kS := nat_lit 2) (wd := V.base.gWs.getD 3 []) (r := GT 3)
    (c := permOK 4060 12 (mask 12) (Nat.mul 4060 12) (GT 3) (GTI 3)) (t := PAT 10) (by quickRfl)
theorem k_g4 : bAnd(wordEqK 4060 12 (mask 12) (pidn 4060 12) GP GPI (nat_lit 2) (V.base.gWs.getD 4 [])
    (GT 4), permOK 4060 12 (mask 12) (Nat.mul 4060 12) (GT 4) (GTI 4)) = true :=
  eA (kS := nat_lit 2) (wd := V.base.gWs.getD 4 []) (r := GT 4)
    (c := permOK 4060 12 (mask 12) (Nat.mul 4060 12) (GT 4) (GTI 4)) (t := PAT 11) (by quickRfl)
theorem k_g5 : bAnd(wordEqK 4060 12 (mask 12) (pidn 4060 12) GP GPI (nat_lit 2) (V.base.gWs.getD 5 [])
    (GT 5), permOK 4060 12 (mask 12) (Nat.mul 4060 12) (GT 5) (GTI 5)) = true :=
  eA (kS := nat_lit 2) (wd := V.base.gWs.getD 5 []) (r := GT 5)
    (c := permOK 4060 12 (mask 12) (Nat.mul 4060 12) (GT 5) (GTI 5)) (t := PAT 12) (by quickRfl)
theorem k_g6 : bAnd(wordEqK 4060 12 (mask 12) (pidn 4060 12) GP GPI (nat_lit 2) (V.base.gWs.getD 6 [])
    (GT 6), permOK 4060 12 (mask 12) (Nat.mul 4060 12) (GT 6) (GTI 6)) = true :=
  eA (kS := nat_lit 2) (wd := V.base.gWs.getD 6 []) (r := GT 6)
    (c := permOK 4060 12 (mask 12) (Nat.mul 4060 12) (GT 6) (GTI 6)) (t := PAT 13) (by quickRfl)
theorem k_g7 : bAnd(wordEqK 4060 12 (mask 12) (pidn 4060 12) GP GPI (nat_lit 2) (V.base.gWs.getD 7 [])
    (GT 7), permOK 4060 12 (mask 12) (Nat.mul 4060 12) (GT 7) (GTI 7)) = true :=
  eA (kS := nat_lit 2) (wd := V.base.gWs.getD 7 []) (r := GT 7)
    (c := permOK 4060 12 (mask 12) (Nat.mul 4060 12) (GT 7) (GTI 7)) (t := PAT 14) (by quickRfl)

theorem k_exRel : exRel 4060 12 (RE.G 0) (RE.G 1) (RE.G 2) 3 = true := by quickRfl

@[expose] noncomputable def exA (k : Nat) : Nat := [1, 0, 0, 0, 2, 0, 3].getD k 0

@[expose] noncomputable def exB (k : Nat) : Nat := [0, 1, 0, 4, 4, 3, 3].getD k 0

@[expose] noncomputable def exC (k : Nat) : Nat := [0, 0, 1, 4, 2, 2, 1].getD k 0

@[expose] noncomputable def exGF (k : Nat) : Bool :=
  exGen 4060 12 (RE.G 0) (RE.G 1) (RE.G 2) (RE.G k) (exA k) (exB k) (exC k)

#kc_each CertificateChecks.KernelCoreD2K.RuFive.exGF 0 7

#kc_forall_chunks exGF_all (fun k => exGF k = true) 7
  CertificateChecks.KernelCoreD2K.RuFive.exGF 1

theorem k_pts : (nfPts 12 (RE.G 0) (RE.G 1) (RE.G 2) 0).Nodup := by decide +kernel

theorem k_nab : nabK 4060 12 V.base.eW.length RE.G = true := by quickRfl
theorem k_cen : cenK 4060 12 5 V.base.eW.length RE.G = true := by quickRfl
theorem k_lines : linesK 4060 12 5 V RE.G = true := by
  have hn : Nat.beq V.ys.length (Nat.succ 5) = true := by quickRfl
  have hv : allN V.ys.length (fun i => bAnd(Nat.blt (V.ys.getD i (nat_lit 0)) V.base.eW.length,
      vK 4060 12 5 (RE.G (nat_lit 0)) (RE.G (V.ys.getD i (nat_lit 0))))) = true := by quickRfl
  have hl : V.ys.length = 6 := Nat.eq_of_beq_eq_true hn
  unfold linesK
  refine (CFSG.KS.PK.strictB_eq _ _).trans ?_
  rw [CFSG.KS.PK.bAnd_eq, CFSG.KS.PK.bAnd_eq, hn, hv, Bool.true_and, Bool.true_and]
  refine CFSG.KS.PK.allN_iff.2 fun j hj => ?_
  have hj6 : j < 6 := lt_of_lt_of_eq hj hl
  rw [CFSG.KS.PK.strictB_eq]
  refine CFSG.KS.PK.allN_iff.2 fun i hi => ?_
  have h := CFSG.KS.PK.allN_iff.1 (rfLnAll i (Nat.lt_trans hi hj6)) j hj6
  have hb : Nat.blt i j = true := Nat.blt_eq.mpr hi
  beta_reduce at h
  rw [hb, CFSG.KS.PK.strictB_eq] at h
  exact h
theorem k_kinds : kindsK 4060 12 V RE.G GT = true := by quickRfl

theorem k_wa0 : wordEqK 4060 12 (mask 12) (pidn 4060 12) GT GTI V.base.gWs.length (V.wAs.getD 0 [])
    (GP (nat_lit 0)) = true := eB (t := PBT 0) (by quickRfl)
theorem k_wa1 : wordEqK 4060 12 (mask 12) (pidn 4060 12) GT GTI V.base.gWs.length (V.wAs.getD 1 [])
    (GP (nat_lit 0)) = true := eB (t := PBT 1) (by quickRfl)
theorem k_wa2 : wordEqK 4060 12 (mask 12) (pidn 4060 12) GT GTI V.base.gWs.length (V.wAs.getD 2 [])
    (GP (nat_lit 0)) = true := eB (t := PBT 2) (by quickRfl)
theorem k_wa3 : wordEqK 4060 12 (mask 12) (pidn 4060 12) GT GTI V.base.gWs.length (V.wAs.getD 3 [])
    (GP (nat_lit 0)) = true := eB (t := PBT 3) (by quickRfl)
theorem k_wa4 : wordEqK 4060 12 (mask 12) (pidn 4060 12) GT GTI V.base.gWs.length (V.wAs.getD 4 [])
    (GP (nat_lit 0)) = true := eB (t := PBT 4) (by quickRfl)
theorem k_wa5 : wordEqK 4060 12 (mask 12) (pidn 4060 12) GT GTI V.base.gWs.length (V.wAs.getD 5 [])
    (GP (nat_lit 0)) = true := eB (t := PBT 5) (by quickRfl)
theorem k_wb0 : wordEqK 4060 12 (mask 12) (pidn 4060 12) GT GTI V.base.gWs.length (V.wBs.getD 0 [])
    (GP (nat_lit 1)) = true := eB (t := PBT 6) (by quickRfl)
theorem k_wb1 : wordEqK 4060 12 (mask 12) (pidn 4060 12) GT GTI V.base.gWs.length (V.wBs.getD 1 [])
    (GP (nat_lit 1)) = true := eB (t := PBT 7) (by quickRfl)
theorem k_wb2 : wordEqK 4060 12 (mask 12) (pidn 4060 12) GT GTI V.base.gWs.length (V.wBs.getD 2 [])
    (GP (nat_lit 1)) = true := eB (t := PBT 8) (by quickRfl)
theorem k_wb3 : wordEqK 4060 12 (mask 12) (pidn 4060 12) GT GTI V.base.gWs.length (V.wBs.getD 3 [])
    (GP (nat_lit 1)) = true := eB (t := PBT 9) (by quickRfl)
theorem k_wb4 : wordEqK 4060 12 (mask 12) (pidn 4060 12) GT GTI V.base.gWs.length (V.wBs.getD 4 [])
    (GP (nat_lit 1)) = true := eB (t := PBT 10) (by quickRfl)
theorem k_wb5 : wordEqK 4060 12 (mask 12) (pidn 4060 12) GT GTI V.base.gWs.length (V.wBs.getD 5 [])
    (GP (nat_lit 1)) = true := eB (t := PBT 11) (by quickRfl)

theorem k_wok : allN (nat_lit 6) (fun i => bAnd(wordOK V i (V.wAs.getD i []),
    wordOK V i (V.wBs.getD i []))) = true := by quickRfl
theorem k_strict : allN (nat_lit 6) (fun i => bAnd(wordOKOne V i (V.wAs.getD i []),
    wordOKOne V i (V.wBs.getD i []))) = true := by quickRfl

end CertificateChecks.KernelCoreD2K.RuFive

end
