module

public import Certificates.Kernel.LocalComp.HeGS36
public import Certificates.Data.Kernel.CF23L34.RegRun1
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.HeGSR

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.PermTool CFSG.KC.CF23L34
open CFSG.Sporadic.SmallOddCore CFSG.ComponentClassification.GrSLit.HeGS
open CertificateChecks.KernelLC.HeFix CertificateChecks.KernelLC.HeGS36

@[expose] def ew (k : Nat) : List Nat := heDWords.getD (k % 5) []

@[expose] noncomputable def R0 : List (Nat × Nat) :=
  (List.range 10).map fun k =>
    if k < 5 then (K (ew k), K (ew k).reverse)
    else (pc (pc gT (K (ew k))) gI, pc (pc gT (K (ew k).reverse)) gI)

theorem ch22702_g : Nat.beq (pc gT (HG.F 0)) (pc (K heGSVWord) gT) = true := by
  quickRfl

theorem ch22702_run :
    (Nat.beq ((rRun1 pc (pidn 8330 14) R0 heGSProg).getD 133 (0, 0)).1 (HG.F 0) &&
      Nat.beq ((rRun1 pc (pidn 8330 14) R0 heGSProg).getD 134 (0, 0)).1 (HG.F 1)) = true := by
  quickRfl

end CertificateChecks.KernelLC.HeGSR

end
