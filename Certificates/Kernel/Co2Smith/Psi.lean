module

public import Certificates.Kernel.Co2Smith.Pts
public import Certificates.Kernel.Sporadic.Co2.ChainA
public import CFSG.Certificates.Kernel.Misc.ArrEnumOps
public import CFSG.Certificates.Kernel.LocalQTCovTPrim
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Co1F2 CFSG.KC.Co2Smith CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.Sporadic.Co2Smith.Native CFSG.Sporadic.Co2Cert CFSG.Monster.B.Co2.Native
open CFSG.Certificates.Native CertificateChecks.KernelSpor

@[expose] noncomputable def CK : Nat :=
  CFSG.KS.Raw.wordK 2300 12 (mask 12) (pidn 2300 12) Co2A.S Co2A.SI glCWord

@[expose] noncomputable def CIK : Nat := pinvS 2300 12 (mask 12) CK

theorem sz_ok : CFSG.KS.Raw.szOK 2300 12 = true := by decide

theorem strong_permB : allN 11 (fun j => CFSG.KC.Misc.ArrEnum.permB 2300 12 (Co2A.S j) &&
    CFSG.KC.Misc.ArrEnum.permB 2300 12 (Co2A.SI j)) = true := by
  decide +kernel

theorem cWord_ok : lettersOK 11 glCWord = true := by decide +kernel

theorem strong_size : co2StrongArrs.size = 11 := Co2A.binds.2.2.2.1

theorem cArr_eq : glCArr = unpack 2300 12 CK := by
  have hp := strong_permB
  unfold glCArr CK
  refine CFSG.KC.Misc.ArrEnum.wordA_unpack sz_ok (j := 11) (fun h hh => Co2A.binds.2.2.2.2.1 h hh)
    (fun h hh => ?_) (fun h hh => ?_) (fun h hh => ?_) cWord_ok
  · rw [Orb.rawInvs_get (by rw [strong_size]; exact hh), Co2A.binds.2.2.2.2.1 h hh]
    exact CFSG.KC.LQT.Cov.T.invCand_unpack (allN_spec Co2A.perm h hh)
  · have := allN_spec hp h hh
    simp only [Bool.and_eq_true] at this
    exact this.1
  · have := allN_spec hp h hh
    simp only [Bool.and_eq_true] at this
    exact this.2

theorem CK_permB : CFSG.KC.Misc.ArrEnum.permB 2300 12 CK = true := by
  have hp := strong_permB
  refine CFSG.KC.Misc.ArrEnum.permB_wordK sz_ok (j := 11) (fun h hh => ?_) (fun h hh => ?_)
    cWord_ok
  · have := allN_spec hp h hh
    simp only [Bool.and_eq_true] at this
    exact this.1
  · have := allN_spec hp h hh
    simp only [Bool.and_eq_true] at this
    exact this.2

theorem cInv_eq : glCInv = unpack 2300 12 CIK := by
  unfold glCInv
  rw [cArr_eq]
  exact CFSG.KC.LQT.Cov.T.invCand_unpack CK_permB

theorem CIK_lt : ∀ i < 2300, pg 12 (mask 12) CIK i < 2300 := by
  obtain ⟨hpr, hs⟩ := CFSG.KC.LQT.Cov.T.perm_facts CK_permB
  intro j hj
  obtain ⟨i, hi, e⟩ := hs j hj
  unfold CIK
  rw [← e, (hpr i hi).2]
  exact hi

theorem psi_eq {A G : Nat} (hb : bindVK (KernelSporSch.Co2M.PV 0) G (trK 22 A) = true) :
    glPsiArr (unpackR 22 A) =
      unpack 2300 12 (pcomp 2300 12 (mask 12) (pcomp 2300 12 (mask 12) CK G) CIK) := by
  unfold glPsiArr
  rw [cArr_eq, permArr_eq hb, cInv_eq,
    CFSG.KC.LQT.Cov.T.compA_unpack (by norm_num) (fun i hi => (bind_facts hb hi).1),
    CFSG.KC.LQT.Cov.T.compA_unpack (by norm_num) CIK_lt]

end CertificateChecks.KernelCo2Smith
