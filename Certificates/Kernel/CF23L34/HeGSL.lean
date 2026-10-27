module

public import Certificates.Kernel.LocalComp.HeGS36
public import Certificates.Kernel.Sporadic.OddCore.HL
public import Certificates.Data.Kernel.HeFixK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.HeGSL

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Mathieu CFSG.KC.PermTool
open CFSG.ComponentClassification.GrSLit.HeldFix CFSG.ComponentClassification.GrSLit.HeGS
open CFSG.Sporadic.SmallOddCore CertificateChecks.KernelLC.HeFix CertificateChecks.KernelLC.HeGS36
open CertificateChecks.KernelSpor

@[expose] noncomputable def fixOm (p : Nat) : Bool :=
  allN 105 (fun k => Nat.blt (nget HeL.omL k) 8330 &&
    Nat.beq (pg 14 (mask 14) p (nget HeL.omL k)) (nget HeL.omL k))

@[expose] noncomputable def not346 (p : Nat) : Bool :=
  !Nat.beq (CFSG.KC.HeFixK.fixK 8330 14 p) 346

theorem ch22701_c0 :
    allN 9 (fun j => Nat.beq (pc (CertificateChecks.KernelSporSch.HeB14.C0 j)
      (CertificateChecks.KernelSporSch.HeB14.C0 j)) (pidn 8330 14)) = true := by
  quickRfl

theorem ch22701_t0 : (Nat.beq (K (heGSComm2 heGST0Comm)) (HG.F 0) && fixOm (HG.F 0)) = true := by
  quickRfl

theorem ch22701_u : (fixOm (K (heGSComm2 heGSUComm)) &&
    !Nat.beq (K (heGSComm2 heGSUComm)) (pidn 8330 14) &&
    !Nat.beq (K (heGSComm2 heGSUComm)) (HG.F 0)) = true := by
  quickRfl

theorem ch22701_v : (Nat.beq (pc (K heGSVWord) (K heGSVWord)) (pidn 8330 14) &&
    !Nat.beq (K heGSVWord) (pidn 8330 14) &&
    Nat.beq (CFSG.KC.HeFixK.fixK 8330 14 (K heGSVWord)) 346) = true := by
  quickRfl

theorem ch22701_fix : (not346 (K (heDWords.getD 1 [])) &&
    not346 (K (heGSComm2 heGSUComm ++ heDWords.getD 1 [])) &&
    not346 (K (0 :: (heGSComm2 heGSUComm ++ heDWords.getD 1 [])))) = true := by
  quickRfl

theorem ch22701_comm :
    (!Nat.beq (pc (K (heDWords.getD 0 [])) (K heGSVWord))
        (pc (K heGSVWord) (K (heDWords.getD 0 []))) &&
      !Nat.beq (pc (K (heDWords.getD 0 [])) (K (heDWords.getD 1 [])))
        (pc (K (heDWords.getD 1 [])) (K (heDWords.getD 0 [])))) = true := by
  quickRfl

theorem ch22701_reps : allN 8 (fun i => !Nat.beq (pcomp 105 7 (mask 7) (HOF.R (Nat.add i 2))
    (HOF.R (Nat.add i 2))) (pidn 105 7)) = true := by
  quickRfl

end CertificateChecks.KernelLC.HeGSL

end
