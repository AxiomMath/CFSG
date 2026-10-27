module

public import Certificates.Data.TitsAschbacherFive
public import Certificates.Kernel.EvenBN.K27585R
public import Certificates.Kernel.MaxD2.TitsD.TransGlue
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Certificate7050Base

public section

set_option maxRecDepth 400000

namespace CertificateChecks.Batch27585

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.BfsPin
open CFSG.Monster.B.Co2.Native CFSG.PSL3Four.Native
open CFSG.Sporadic.Schreier.Tits CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Tits2268
open CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.TitsCommon CertificateChecks.KernelSporSch.TitsCentral
open CertificateChecks.KernelSporSch.TitsHelp CertificateChecks.KernelEvenBN
open CertificateChecks.KernelEvenBN.Five
open Certificates.TitsAschbacherParrott Certificates.TitsAschbacherE32 Certificates.TitsAschbacherFive
open Certificates.MaxD2Perm

theorem conj_comm {a u b : Nat} (ha : CFSG.KS.MaxD2.Cn 1755 11 a) (hu : CFSG.KS.MaxD2.Cn 1755 11 u)
    (hb : CFSG.KS.MaxD2.Cn 1755 11 b) (hp : permOK 1755 11 (mask 11) (1755 * 11) a b = true) :
    pcomp 1755 11 (mask 11) (pcomp 1755 11 (mask 11) (pcomp 1755 11 (mask 11) a u) b) a =
      pcomp 1755 11 (mask 11) a u := by
  have hn := KernelEvenBN.szOK1755
  refine CFSG.KS.MaxD2.u_inj (CFSG.KS.MaxD2.cc (CFSG.KS.MaxD2.cc (CFSG.KS.MaxD2.cc ha hu) hb) ha)
    (CFSG.KS.MaxD2.cc ha hu) (CFSG.KS.MaxD2.tab_ext (CFSG.KS.MaxD2.size_u _)
      (CFSG.KS.MaxD2.size_u _) fun x hx => ?_)
  have hax := CFSG.KS.MaxD2.canon_lt ha hx
  rw [CFSG.KS.MaxD2.get_u hx, CFSG.KS.MaxD2.get_u hx, CFSG.KS.MaxD2.pg_pc hn hx,
    CFSG.KS.MaxD2.pg_pc hn hax, ((CFSG.KS.MaxD2.perm_spec hp).1 x hx).2]

theorem trans_ok : transCheck () = true := by
  have H := KernelMaxD2.TitsD.hyps
  have hn := KernelEvenBN.szOK1755
  unfold transCheck
  simp only []
  rw [(CFSG.KS.MaxD2.rEnum_eq H).1, (CFSG.KS.MaxD2.nEnum_eq H.toM).1,
    CFSG.KS.MaxD2.wT_u H.toM KernelMaxD2.TitsD.k_rg0]
  dsimp only [KernelMaxD2.TitsD.KD]
  refine CFSG.KS.MaxD2.allBelow_iff'.2 fun k hk => ?_
  rw [CFSG.KS.MaxD2.rec_size] at hk
  have hc := (PK.allN_iff.1 KernelMaxD2.TitsD.k_cj) k hk
  have hr : C (KernelMaxD2.TitsD.RE.T k) := CFSG.KS.MaxD2.rt_canon H hk
  have hu : C (KernelMaxD2.TitsD.RE.G 0) := (H.hRG 0 (by decide)).2
  rw [CFSG.KS.MaxD2.rec_get hk, Bool.or_eq_true]
  by_cases e : Nat.beq (KernelMaxD2.TitsD.RE.T k) (pidn 1755 11) = true
  · left
    change (unpack 1755 11 (KernelMaxD2.TitsD.RE.T k) == idTab 1755) = true
    rw [Nat.eq_of_beq_eq_true e, CFSG.KS.MaxD2.id_u hn]
    exact beq_self_eq_true _
  · right
    have h2 := CFSG.KS.MaxD2.bif_f (Bool.eq_false_iff.2 e) hc
    obtain ⟨hj, he⟩ := CFSG.KS.MaxD2.band_e h2
    have hj' := Nat.blt_eq.mp hj
    have hiv := KernelMaxD2.TitsD.inv_all hj'
    have ha : C (KernelMaxD2.TitsD.NE.T (r32 KernelMaxD2.TitsD.CJ k)) :=
      CFSG.KS.MaxD2.nt_canon H.toM hj'
    have hb : C (KernelMaxD2.TitsD.NE.T (r32 KernelMaxD2.TitsD.INV (r32 KernelMaxD2.TitsD.CJ k))) :=
      CFSG.KS.MaxD2.nt_canon H.toM hiv.1
    rw [CFSG.KS.MaxD2.anyBelow_iff]
    refine ⟨r32 KernelMaxD2.TitsD.CJ k, by rw [CFSG.KS.MaxD2.rec_size]; exact hj', ?_⟩
    rw [CFSG.KS.MaxD2.rec_get hj', cmpU ha hu, cmpU hr ha, eqU (cmpC ha hu) (cmpC hr ha),
      Nat.eq_of_beq_eq_true he, conj_comm ha hu hb hiv.2]
    exact Nat.beq_refl _

set_option simprocs false in
theorem five_ok : fiveCheck () = true := by
  obtain ⟨hx, cx⟩ := chain_gen bindsH canH (w := hatXWord) (by decide)
  obtain ⟨hu, cu⟩ := chain_gen bindsH canH (w := u2Word) (by decide)
  obtain ⟨hh, ch⟩ := chain_gen bindsH canH (w := deltaHWord) (by decide)
  have l := lK
  simp only [Bool.and_eq_true] at l
  obtain ⟨⟨la, lb⟩, lu⟩ := l
  have k := cK
  simp only [Bool.and_eq_true] at k
  obtain ⟨⟨ca, cb⟩, cU⟩ := k
  have r := rel
  simp only [Five.pc, Bool.and_eq_true] at r
  obtain ⟨⟨r1, r2⟩, r3⟩ := r
  have cX : C X := cx
  have cU2 : C U2 := cu
  have cd : C Dl := cmpC (cmpC ch (powC (cmpC ca canonZ))) cb
  have hx' : xArr = unpack 1755 11 X := hx
  have hu' : u2Arr () = unpack 1755 11 U2 := hu
  have hd : deltaArr () = unpack 1755 11 Dl := by
    unfold deltaArr hArr Dl Hd Five.pc deltaExp
    rw [hh, wT_eq la, wT_eq lb, z_eq, cmpU ca canonZ, powU (cmpC ca canonZ),
      cmpU ch (powC (cmpC ca canonZ)), cmpU (cmpC ch (powC (cmpC ca canonZ))) cb]
  unfold fiveCheck
  simp only [hu', hx', hd, z_eq, vA_eq (i := 2) (by decide), wT_eq lu, trans_ok]
  simp (config := { maxDischargeDepth := 12 }) only [cmpU, cmpC, eqU, powU, powC, cX, cU2, cd,
    cU, canonZ, cV (i := 2) (by decide)]
  simp only [r1, r2, r3, Bool.and_true]
  decide

end CertificateChecks.Batch27585

namespace Certificates

open CertificateChecks

theorem certificate27585 : Certificates.TitsAschbacherFive.fiveCheck () = true := CertificateChecks.Batch27585.five_ok

end Certificates
