module

public import Certificates.Kernel.Co1B.PrimD2045
public import Certificates.Kernel.Co1B.OrbK2045
public import Certificates.Data.Kernel.MergeReplay
public import Certificates.Data.Kernel.MergeG
public import Certificates.Data.Kernel.Spor.Prim
public meta import Certificates.Kernel.Co1B.GenTri2045
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Prim2045

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CFSG.KC.MergeR CFSG.KC.MergeG
  CertificateChecks.KernelCo1B.Tri2045

@[expose] noncomputable def rI (l k : Nat) : Nat := pg 11 2047 (PD.LP l) (Nat.mul 3 k)

@[expose] noncomputable def rU (l k : Nat) : Nat := pg 11 2047 (PD.LP l) (Nat.add (Nat.mul 3 k) 1)

@[expose] noncomputable def rV (l k : Nat) : Nat := pg 11 2047 (PD.LP l) (Nat.add (Nat.mul 3 k) 2)

@[expose] noncomputable def seg0 (s : Nat) : Bool :=
  segCG 1365 11 2 RO.S (PD.CNT 0) 32 (PD.TP 0) (PD.PP 0) PD.A0 (rI 0) (rU 0) (rV 0) s

@[expose] noncomputable def seg1 (s : Nat) : Bool :=
  segCG 1365 11 2 RO.S (PD.CNT 1) 32 (PD.TP 1) (PD.PP 1) PD.A1 (rI 1) (rU 1) (rV 1) s

@[expose] noncomputable def seg2 (s : Nat) : Bool :=
  segCG 1365 11 2 RO.S (PD.CNT 2) 32 (PD.TP 2) (PD.PP 2) PD.A2 (rI 2) (rU 2) (rV 2) s

end CertificateChecks.KernelCo1B.Prim2045

#kc_slices CertificateChecks.KernelCo1B.Prim2045.M0 CertificateChecks.KernelCo1B.Prim2045.seg0 43
#kc_slices CertificateChecks.KernelCo1B.Prim2045.M1 CertificateChecks.KernelCo1B.Prim2045.seg1 43
#kc_slices CertificateChecks.KernelCo1B.Prim2045.M2 CertificateChecks.KernelCo1B.Prim2045.seg2 43

namespace CertificateChecks.KernelCo1B.Prim2045

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CFSG.KC.MergeR CFSG.KS.Prim
  CertificateChecks.KernelCo1B.Tri2045

theorem kCan : allN 2 (fun i => canonK 1365 11 (mask 11) (1365 * 11) (RO.S i)) = true := by
  quickRfl

theorem kS0 : searchK 1365 11 2047 15015 2 RO.S 0 1 (PD.CNT 0) (PD.LP 0) = true := by quickRfl
theorem kS1 : searchK 1365 11 2047 15015 2 RO.S 0 5 (PD.CNT 1) (PD.LP 1) = true := by quickRfl
theorem kS2 : searchK 1365 11 2047 15015 2 RO.S 0 83 (PD.CNT 2) (PD.LP 2) = true := by quickRfl

theorem kH0 : bAnd(Nat.blt 0 1365, bAnd(Nat.blt 1 1365, bAnd(Nat.blt (PD.CNT 0) 4096,
    bAnd(Nat.blt 0 32, Nat.ble (PD.CNT 0) (Nat.mul 32 43))))) = true := by quickRfl
theorem kH1 : bAnd(Nat.blt 0 1365, bAnd(Nat.blt 5 1365, bAnd(Nat.blt (PD.CNT 1) 4096,
    bAnd(Nat.blt 0 32, Nat.ble (PD.CNT 1) (Nat.mul 32 43))))) = true := by quickRfl
theorem kH2 : bAnd(Nat.blt 0 1365, bAnd(Nat.blt 83 1365, bAnd(Nat.blt (PD.CNT 2) 4096,
    bAnd(Nat.blt 0 32, Nat.ble (PD.CNT 2) (Nat.mul 32 43))))) = true := by quickRfl

theorem kA0 : allN 1365 (fun y => Nat.beq (pgW 11 (PD.A0 0) y) (nIf(Nat.beq y 1, 0, y))) = true :=
  by quickRfl
theorem kA1 : allN 1365 (fun y => Nat.beq (pgW 11 (PD.A1 0) y) (nIf(Nat.beq y 5, 0, y))) = true :=
  by quickRfl
theorem kA2 : allN 1365 (fun y => Nat.beq (pgW 11 (PD.A2 0) y) (nIf(Nat.beq y 83, 0, y))) = true :=
  by quickRfl

theorem kT0 : allN 1365 (fun l => Nat.ble (pgW 12 (PD.TP 0) l) (PD.CNT 0)) = true := by quickRfl
theorem kT1 : allN 1365 (fun l => Nat.ble (pgW 12 (PD.TP 1) l) (PD.CNT 1)) = true := by quickRfl
theorem kT2 : allN 1365 (fun l => Nat.ble (pgW 12 (PD.TP 2) l) (PD.CNT 2)) = true := by quickRfl

theorem kC0 : Nat.beq (mergeCnt 1365 11 RO.S (PD.CNT 0) 32 (PD.TP 0) (PD.PP 0) PD.A0 (rI 0) (rU 0)
    (rV 0)) (timedCnt 1365 (PD.CNT 0) (PD.TP 0)) = true := by quickRfl
theorem kC1 : Nat.beq (mergeCnt 1365 11 RO.S (PD.CNT 1) 32 (PD.TP 1) (PD.PP 1) PD.A1 (rI 1) (rU 1)
    (rV 1)) (timedCnt 1365 (PD.CNT 1) (PD.TP 1)) = true := by quickRfl
theorem kC2 : Nat.beq (mergeCnt 1365 11 RO.S (PD.CNT 2) 32 (PD.TP 2) (PD.PP 2) PD.A2 (rI 2) (rU 2)
    (rV 2)) (timedCnt 1365 (PD.CNT 2) (PD.TP 2)) = true := by quickRfl

theorem kF0 : finalC 1365 11 (PD.CNT 0) 43 (PD.TP 0) PD.A0 = true := by quickRfl
theorem kF1 : finalC 1365 11 (PD.CNT 1) 43 (PD.TP 1) PD.A1 = true := by quickRfl
theorem kF2 : finalC 1365 11 (PD.CNT 2) 43 (PD.TP 2) PD.A2 = true := by quickRfl

end CertificateChecks.KernelCo1B.Prim2045

end
