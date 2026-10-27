module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallHeModelInputs
public meta import CFSG.Sporadic.HeldB.InnerRestrict
public meta import CFSG.Sporadic.HeldB.OuterCentRestrict
public meta import CFSG.GH74.KGroups.PermCheck
public import Certificates.Kernel.Census.CatFacts.C2010P
public import CFSG.Certificates.Kernel.SporSch.MOCChain
public import CFSG.Certificates.Kernel.SporSch.ChainKPack
import Mathlib.Tactic.IntervalCases

public section

namespace CertificateChecks.KernelCatFacts

open CFSG.ComponentClassification.CatFactsSmall.He CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
  CFSG.KS.M11 CFSG.KS.SporSch.MOC CFSG.Sporadic.Schreier CFSG.Sporadic.HeldB CFSG.Monster.B.Co2
  CFSG.Monster.B.Mathieu CertificateChecks.KernelLQT.He4148 CertificateChecks.KernelCatFacts.C2010P

theorem repG {j : Nat} (hj : j < heInnerSigma0.length) :
    CFSG.Monster.B.Co2.Rep 240 (unpack 240 8 (SG j)) (heInnerSigmaP0 j) ∧
      canonK 240 8 (mask 8) (240 * 8) (SG j) = true := by
  have h := bindsK_spec bSG j hj
  rw [Nat.zero_add] at h
  exact ⟨(bind_facts h).2.2.1, h.2.2.2.1⟩

theorem repU {j : Nat} (hj : j < 2) :
    CFSG.Monster.B.Co2.Rep 98 (unpack 98 7 (SU j)) (permOrId 98 ([heSigma1, heSigma2].getD j #[])) ∧
      canonK 98 7 (mask 7) (98 * 7) (SU j) = true := by
  have h := bindsK_spec bSU j (by simpa using hj)
  rw [Nat.zero_add] at h
  exact ⟨(bind_facts h).2.2.1, h.2.2.2.1⟩

theorem img_y00 : imageList y00 = (unpack 240 8 (QA.S 0)).toList := by
  obtain ⟨c1, c2, e, -⟩ := eA0
  obtain ⟨r3, k3⟩ := repG (j := 3) (by decide)
  obtain ⟨r8, k8⟩ := repG (j := 8) (by decide)
  obtain ⟨r4, k4⟩ := repG (j := 4) (by decide)
  obtain ⟨r1, k1⟩ := repG (j := 1) (by decide)
  have h := rep_pcomp c2 k1 (rep_pcomp c1 k4 (rep_pcomp k3 k8 r3 r8) r4) r1
  rw [Nat.eq_of_beq_eq_true e] at h
  exact imageList_of_rep (unpack_size' _ _ _) h

theorem img_y01 : imageList y01 = (unpack 240 8 (QA.S 1)).toList := by
  obtain ⟨c1, c2, c3, c4, e, -⟩ := eA1
  obtain ⟨r6, k6⟩ := repG (j := 6) (by decide)
  obtain ⟨r4, k4⟩ := repG (j := 4) (by decide)
  obtain ⟨r1, k1⟩ := repG (j := 1) (by decide)
  obtain ⟨r7, k7⟩ := repG (j := 7) (by decide)
  obtain ⟨r5, k5⟩ := repG (j := 5) (by decide)
  have h := rep_pcomp c4 k5 (rep_pcomp c3 k4 (rep_pcomp c2 k7 (rep_pcomp c1 k1
    (rep_pcomp k6 k4 r6 r4) r1) r7) r4) r5
  rw [Nat.eq_of_beq_eq_true e] at h
  exact imageList_of_rep (unpack_size' _ _ _) h

theorem img_yu0 : imageList yu0 = (unpack 98 7 (QB.S 0)).toList := by
  obtain ⟨c1, c2, c3, c4, c5, e, -⟩ := eB0
  obtain ⟨r1, k1⟩ := repU (j := 0) (by decide)
  obtain ⟨r2, k2⟩ := repU (j := 1) (by decide)
  have h := rep_pcomp c5 k1 (rep_pcomp c4 k2 (rep_pcomp c3 k1 (rep_pcomp c2 k1
    (rep_pcomp c1 k2 (rep_pcomp k2 k1 r2 r1) r2) r1) r1) r2) r1
  rw [Nat.eq_of_beq_eq_true e] at h
  exact imageList_of_rep (unpack_size' _ _ _) h

theorem img_yu1 : imageList yu1 = (unpack 98 7 (QB.S 1)).toList := by
  obtain ⟨c1, c2, c3, c4, c5, e, -⟩ := eB1
  obtain ⟨r1, k1⟩ := repU (j := 0) (by decide)
  obtain ⟨r2, k2⟩ := repU (j := 1) (by decide)
  have h := rep_pcomp c5 k1 (rep_pcomp c4 k2 (rep_pcomp c3 k1 (rep_pcomp c2 k2
    (rep_pcomp c1 k1 (rep_pcomp k2 k1 r2 r1) r1) r2) r1) r2) r1
  rw [Nat.eq_of_beq_eq_true e] at h
  exact imageList_of_rep (unpack_size' _ _ _) h

theorem order5 {n w P : Nat} {g : Equiv.Perm (Fin n)} (hsz : szOK n w = true)
    (hg : imageList g = (unpack n w P).toList) (hc : canonK n w (mask w) (n * w) P = true)
    (h : ordIs n w (mask w) (pidn n w) P 4 = true) : orderIs g 5 = true :=
  (orderIs_iff g (by norm_num)).2
    (ordIs_orderOf hsz (prep_of_imageList hg) (PF.canon_facts hc).2.2.1 (by norm_num) h)

theorem chainA : ChainK 240 8 [tab y00, tab y01] wY0 (#v[0, 1, 2] : Vector (Fin 240) 3) QA.S QA.SI
    QA.LR QA.TR QA.TRI 5 QA.BP 15 16 := by
  refine ⟨by norm_num, by norm_num, by norm_num, fun j hj => ?_, by decide, QA.head, QA.hl,
    by norm_num, QA.hs⟩
  have hj' : j < 2 := by simpa using hj
  interval_cases j
  · simpa only [List.getD_cons_zero, tab_eq] using img_y00
  · simpa only [List.getD_cons_succ, List.getD_cons_zero, tab_eq] using img_y01

theorem chainB : ChainK 98 7 [tab yu0, tab yu1] wYu (#v[0, 8] : Vector (Fin 98) 2) QB.S QB.SI
    QB.LR QB.TR QB.TRI 4 QB.BP 7 16 := by
  refine ⟨by norm_num, by norm_num, by norm_num, fun j hj => ?_, by decide, QB.head, QB.hl,
    by norm_num, QB.hs⟩
  have hj' : j < 2 := by simpa using hj
  interval_cases j
  · simpa only [List.getD_cons_zero, tab_eq] using img_yu0
  · simpa only [List.getD_cons_succ, List.getD_cons_zero, tab_eq] using img_yu1

open Certificates in
open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.CatFactsSmall in
open CFSG.ComponentClassification.CatFactsSmall.He CFSG.GH74.KGroups CFSG.Certificates in
open CFSG.Sporadic.Schreier CFSG.Sporadic.HeldB Subgroup in
open CFSG.ComponentClassification.FixedCommutingProduct in
theorem facts2010 : (QY0.check = true ∧ QY0.orderCertificate = 40320)
    ∧ (orderIs y00 5 = true ∧ orderIs y01 5 = true)
    ∧ (QYu.check = true ∧ QYu.orderCertificate = 1080)
    ∧ (orderIs yu0 5 = true ∧ orderIs yu1 5 = true) := by
  obtain ⟨a1, a2⟩ := chainK_check (by decide) (by decide) chainA
  obtain ⟨b1, b2⟩ := chainK_check (by decide) (by decide) chainB
  obtain ⟨o1, o2, o3, o4⟩ := oY
  obtain ⟨-, -, -, ca0⟩ := eA0
  obtain ⟨-, -, -, -, -, ca1⟩ := eA1
  obtain ⟨-, -, -, -, -, -, cb0⟩ := eB0
  obtain ⟨-, -, -, -, -, -, cb1⟩ := eB1
  refine ⟨⟨a1, a2.trans (Nat.eq_of_beq_eq_true oQ.1)⟩, ⟨order5 szA img_y00 ca0 o1,
    order5 szA img_y01 ca1 o2⟩, ⟨b1, b2.trans (Nat.eq_of_beq_eq_true oQ.2)⟩,
    ⟨order5 szB img_yu0 cb0 o3, order5 szB img_yu1 cb1 o4⟩⟩

end CertificateChecks.KernelCatFacts
