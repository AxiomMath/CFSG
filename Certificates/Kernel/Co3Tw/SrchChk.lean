module

public import Certificates.Data.Kernel.Misc.CentSrch
public import Certificates.Kernel.Sporadic.Co3.C
public import Certificates.Kernel.Co3Tw.SrchData
public import Certificates.Data.Kernel.Misc.ArrEnum
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo3Tw

open CFSG.KC.Enum CFSG.KC.CentSrch CertificateChecks.KernelSpor SD

@[expose] noncomputable def xpK (k : Nat) : Nat :=
  nIf(Nat.beq k 0, xp0, nIf(Nat.beq k 1, xp1, nIf(Nat.beq k 2, xp2, nIf(Nat.beq k 3, xp3,
    nIf(Nat.beq k 4, xp4, nIf(Nat.beq k 5, xp5, xp6))))))

@[expose] noncomputable def ypK (k : Nat) : Nat :=
  nIf(Nat.beq k 0, yp0, nIf(Nat.beq k 1, yp1, nIf(Nat.beq k 2, yp2, nIf(Nat.beq k 3, yp3,
    nIf(Nat.beq k 4, yp4, nIf(Nat.beq k 5, yp5, yp6))))))

theorem ch431008d0 : dOK 276 9 xp0 yp0 dp0 = true := by quickRfl
theorem ch431008d1 : dOK 276 9 xp1 yp1 dp1 = true := by quickRfl
theorem ch431008d2 : dOK 276 9 xp2 yp2 dp2 = true := by quickRfl
theorem ch431008d3 : dOK 276 9 xp3 yp3 dp3 = true := by quickRfl
theorem ch431008d4 : dOK 276 9 xp4 yp4 dp4 = true := by quickRfl
theorem ch431008d5 : dOK 276 9 xp5 yp5 dp5 = true := by quickRfl
theorem ch431008d6 : dOK 276 9 xp6 yp6 dp6 = true := by quickRfl

theorem ch431008g : allN 7 (fun k => bAnd(CFSG.KC.Misc.ArrEnum.permB 276 9 (xpK k),
    CFSG.KC.Misc.ArrEnum.permB 276 9 (ypK k))) = true := by quickRfl

theorem ch431008p0 : planOK 276 9 7 Co3C.BP dp0 pl0 0 = true := by quickRfl
theorem ch431008p1 : planOK 276 9 7 Co3C.BP dp1 pl1 0 = true := by quickRfl
theorem ch431008p2 : planOK 276 9 7 Co3C.BP dp2 pl2 0 = true := by quickRfl
theorem ch431008p3 : planOK 276 9 7 Co3C.BP dp3 pl3 0 = true := by quickRfl
theorem ch431008p4 : planOK 276 9 7 Co3C.BP dp4 pl4 0 = true := by quickRfl
theorem ch431008p5 : planOK 276 9 7 Co3C.BP dp5 pl5 0 = true := by quickRfl
theorem ch431008p6 : planOK 276 9 7 Co3C.BP dp6 pl6 0 = true := by quickRfl

theorem ch431008s0 :
    Nat.beq (srch 276 9 7 Co3C.LR Co3C.TR Co3C.TRI Co3C.BP dp0 ts0 pl0 0 0 0) 486 = true := by quickRfl
theorem ch431008s1 :
    Nat.beq (srch 276 9 7 Co3C.LR Co3C.TR Co3C.TRI Co3C.BP dp1 ts1 pl1 0 0 0) 1458 = true := by quickRfl
theorem ch431008s2 :
    Nat.beq (srch 276 9 7 Co3C.LR Co3C.TR Co3C.TRI Co3C.BP dp2 ts2 pl2 0 0 0) 81 = true := by quickRfl
theorem ch431008s3 :
    Nat.beq (srch 276 9 7 Co3C.LR Co3C.TR Co3C.TRI Co3C.BP dp3 ts3 pl3 0 0 0) 972 = true := by quickRfl
theorem ch431008s4 :
    Nat.beq (srch 276 9 7 Co3C.LR Co3C.TR Co3C.TRI Co3C.BP dp4 ts4 pl4 0 0 0) 972 = true := by quickRfl
theorem ch431008s5 :
    Nat.beq (srch 276 9 7 Co3C.LR Co3C.TR Co3C.TRI Co3C.BP dp5 ts5 pl5 0 0 0) 54 = true := by quickRfl
theorem ch431008s6 :
    Nat.beq (srch 276 9 7 Co3C.LR Co3C.TR Co3C.TRI Co3C.BP dp6 ts6 pl6 0 0 0) 54 = true := by quickRfl

theorem neg431008s5 :
    (!Nat.beq (srch 276 9 7 Co3C.LR Co3C.TR Co3C.TRI Co3C.BP dp5 [] pl5 0 0 0) 54) = true := by quickRfl
theorem neg431008p0 : (!planOK 276 9 7 Co3C.BP dp1 pl0 0) = true := by quickRfl
theorem neg431008d0 : (!dOK 276 9 xp0 yp0 dp1) = true := by quickRfl

end CertificateChecks.KernelCo3Tw

end
