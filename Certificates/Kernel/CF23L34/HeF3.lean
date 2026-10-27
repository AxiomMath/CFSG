module

public import Certificates.Kernel.CF23L34.HeGSL
public import Certificates.Data.GrSLitHeZStar
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.HeF3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.PermTool
open CFSG.ComponentClassification.GrSLit.HeGS
open CertificateChecks.KernelLC.HeFix CertificateChecks.KernelLC.HeGS36

@[expose] noncomputable def avoid (p : Nat) : Bool :=
  !Nat.beq p (pidn 8330 14) && (!Nat.beq p (HG.F 0) &&
    (!Nat.beq p (K (heGSComm2 heGSUComm)) &&
      !Nat.beq p (pc (HG.F 0) (K (heGSComm2 heGSUComm)))))

@[expose] noncomputable def f3OK (a b : Nat) : Bool :=
  Nat.beq (pc a a) (pidn 8330 14) && (Nat.beq (pc b b) (pidn 8330 14) &&
    (Nat.beq (pc a b) (pc b a) && (avoid a && (avoid b && avoid (pc a b)))))

theorem ch22705 : f3OK (K (heGSEW [2, 4, 2, 4])) (K (heGSEW [1])) = true := by
  quickRfl

end CertificateChecks.KernelLC.HeF3

end
