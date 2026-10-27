module

public import Certificates.Kernel.Co3Tw.EnumV3
public import Certificates.Kernel.Co3Tw.EnumV4
public import Certificates.Kernel.Co3Tw.SrchData
public import Certificates.Kernel.Sporadic.Co3.C
public import Certificates.Data.Kernel.Misc.CentSrch
public import Certificates.Data.Kernel.Misc.ArrEnum
public import Certificates.Data.Kernel.Misc.PermWit
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo3Tw

open CFSG.KC.Enum CFSG.KS CFSG.KC.PermWit CFSG.KC.CentSrch CertificateChecks.KernelSpor

@[expose] noncomputable def commP (p q : Nat) : Bool :=
  Nat.beq (pcomp 276 9 (mask 9) p q) (pcomp 276 9 (mask 9) q p)

@[expose] noncomputable def inT (N : Nat) (T : Nat → Nat) (p : Nat) : Bool :=
  !(allN N fun i => !(Nat.beq (T i) p))

@[expose] noncomputable def cenOK (x y p : Nat) : Bool :=
  bAnd(bAnd(CFSG.KC.Misc.ArrEnum.permB 276 9 p, siftR 276 9 Co3C.LR Co3C.TRI Co3C.BP 7 p),
    bAnd(commP p x, commP p y))

@[expose] noncomputable def vOK (ng N : Nat) (G T : Nat → Nat) (x y c : Nat) : Bool :=
  bAnd(bAnd(Nat.beq N (nat_lit 243), allN ng fun k => cenOK x y (G k)),
    bAnd(cenOK x y c,
      bAnd(bAnd(Nat.beq (pcomp 276 9 (mask 9) c c) (pidn 276 9), !(Nat.beq c (pidn 276 9))),
        allN ng fun k => inT N T (pcomp 276 9 (mask 9) (pcomp 276 9 (mask 9) c (G k)) c))))

theorem ch431008v3 : vOK EV3.ng EV3.N EV3.G EV3.T SD.xp3 SD.yp3 VD.c3 = true := by quickRfl
theorem ch431008v4 : vOK EV4.ng EV4.N EV4.G EV4.T SD.xp4 SD.yp4 VD.c4 = true := by quickRfl

theorem ch431008t1 : Nat.beq (srch 276 9 7 Co3C.LR Co3C.TR Co3C.TRI Co3C.BP SD.dp1 [SD.xp1, SD.yp1]
    SD.pl1 0 0 0) 1458 = true := by quickRfl
theorem ch431008t3 : Nat.beq (srch 276 9 7 Co3C.LR Co3C.TR Co3C.TRI Co3C.BP SD.dp3 [SD.xp3, SD.yp3]
    SD.pl3 0 0 0) 972 = true := by quickRfl
theorem ch431008t4 : Nat.beq (srch 276 9 7 Co3C.LR Co3C.TR Co3C.TRI Co3C.BP SD.dp4 [SD.xp4, SD.yp4]
    SD.pl4 0 0 0) 972 = true := by quickRfl
theorem ch431008t6 : Nat.beq (srch 276 9 7 Co3C.LR Co3C.TR Co3C.TRI Co3C.BP SD.dp6 [SD.xp6, SD.yp6]
    SD.pl6 0 0 0) 54 = true := by quickRfl

theorem ch431008ts : bAnd(SD.ts0 == [SD.xp0, SD.yp0], bAnd(SD.ts2 == [SD.xp2, SD.yp2],
    SD.ts5 == [SD.xp5, SD.yp5])) = true := by quickRfl

theorem neg431008v : (!vOK EV3.ng EV3.N EV3.G EV3.T SD.xp4 SD.yp4 VD.c3) = true := by quickRfl
theorem neg431008c : (!vOK EV3.ng EV3.N EV3.G EV3.T SD.xp3 SD.yp3 (pidn 276 9)) = true := by quickRfl

end CertificateChecks.KernelCo3Tw

end
