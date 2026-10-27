module

public import Certificates.Kernel.Co1B.PrimD2045
public import Certificates.Kernel.Co1B.OrbK2045
public import Certificates.Data.Kernel.Spor.CBfsK
public meta import Certificates.Kernel.Co1B.GenTri2045
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Prim2045

open CFSG.KC.Enum CFSG.KS CFSG.KS.CB CertificateChecks.KernelCo1B.Tri2045

@[expose] noncomputable def stp (j x : Nat) : Nat := pg 11 2047 (RO.S (Nat.add j 2)) x

@[expose] noncomputable def tPts (t k : Nat) : Nat := pg 11 2047 (PD.PTS t) k

@[expose] noncomputable def tPos (t z : Nat) : Nat := pg 11 2047 (PD.POS t) z

@[expose] noncomputable def tPar (t k : Nat) : Nat := pg 11 2047 (PD.PAR t) k

@[expose] noncomputable def tLab (t k : Nat) : Nat := pg 11 2047 (PD.LAB t) k

@[expose] noncomputable def ptS (t s : Nat) : Bool :=
  cbPtRange 1365 (PD.M t) 4 stp (tPts t) (tPos t) (tPar t) (tLab t) (Nat.mul s 128) 128

@[expose] noncomputable def pt0 : Nat → Bool := ptS 0
@[expose] noncomputable def pt1 : Nat → Bool := ptS 1
@[expose] noncomputable def pt2 : Nat → Bool := ptS 2
@[expose] noncomputable def pt3 : Nat → Bool := ptS 3

@[expose] noncomputable def posK (t : Nat) : Bool :=
  allN 1365 (cbPos 1365 (PD.M t) (tPts t) (tPos t))

@[expose] noncomputable def covK : Bool :=
  allN 1365 fun z => bIf(Nat.blt (tPos 0 z) (PD.M 0), true, bIf(Nat.blt (tPos 1 z) (PD.M 1), true,
    bIf(Nat.blt (tPos 2 z) (PD.M 2), true, Nat.blt (tPos 3 z) (PD.M 3))))

end CertificateChecks.KernelCo1B.Prim2045

#kc_slices CertificateChecks.KernelCo1B.Prim2045.P0 CertificateChecks.KernelCo1B.Prim2045.pt0 1
#kc_slices CertificateChecks.KernelCo1B.Prim2045.P1 CertificateChecks.KernelCo1B.Prim2045.pt1 8
#kc_slices CertificateChecks.KernelCo1B.Prim2045.P2 CertificateChecks.KernelCo1B.Prim2045.pt2 3
#kc_slices CertificateChecks.KernelCo1B.Prim2045.P3 CertificateChecks.KernelCo1B.Prim2045.pt3 1
#kc_slices CertificateChecks.KernelCo1B.Prim2045.PS CertificateChecks.KernelCo1B.Prim2045.posK 4

namespace CertificateChecks.KernelCo1B.Prim2045

open CFSG.KC.Enum CFSG.KS CFSG.KS.CB CertificateChecks.KernelCo1B.Tri2045

theorem kFix : allN 6 (fun j => bIf(Nat.ble 2 j, Nat.beq (pg 11 (mask 11) (RO.S j) 0) 0,
    Bool.not (Nat.beq (pg 11 (mask 11) (RO.S j) 0) 0))) = true := by quickRfl

theorem kM0 : Nat.beq (PD.M 0) 1 = true := by quickRfl
theorem kM1 : Nat.beq (PD.M 1) 1024 = true := by quickRfl
theorem kM2 : Nat.beq (PD.M 2) 320 = true := by quickRfl
theorem kM3 : Nat.beq (PD.M 3) 20 = true := by quickRfl

theorem kHd0 : cbHead 1365 (PD.M 0) 0 (tPts 0) (tPar 0) (tLab 0) = true := by quickRfl
theorem kHd1 : cbHead 1365 (PD.M 1) 1 (tPts 1) (tPar 1) (tLab 1) = true := by quickRfl
theorem kHd2 : cbHead 1365 (PD.M 2) 5 (tPts 2) (tPar 2) (tLab 2) = true := by quickRfl
theorem kHd3 : cbHead 1365 (PD.M 3) 83 (tPts 3) (tPar 3) (tLab 3) = true := by quickRfl

theorem kCov : covK = true := by quickRfl

end CertificateChecks.KernelCo1B.Prim2045

end
