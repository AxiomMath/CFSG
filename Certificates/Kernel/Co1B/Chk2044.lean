module

public import Certificates.Kernel.Co1B.Tow2044
public import Certificates.Kernel.Co1B.Bfs2044
public import Certificates.Kernel.Co1B.IotaData
public import Certificates.Data.Kernel.SporSch.Co1Cent
public import Certificates.Data.Kernel.SporSch.Co1Bfs
public import Certificates.Data.Kernel.SporSch.Co1Stab
public import Certificates.Data.CFSGNative.Co1.Involutions
public import Certificates.Data.Kernel.Co1F2
public import Certificates.Data.Kernel.Co1B
public import Certificates.Data.Kernel.Co1BW
public import Certificates.Kernel.Co1B.Data2041
public import CFSG.Sporadic.Co1Block.TwoAData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.C2044

open CFSG.KC.Enum CFSG.KS.SporSch.M24 CFSG.KS.SporSch.VOrb CFSG.KC.Co1F2 CFSG.KD.Co1B
  CFSG.Sporadic.Co1Block CFSG.KS.Raw
open CFSG.KC.Co1B (mulWK)

@[expose] noncomputable def IA : Nat := getL CFSG.KC.Co1B.oneK IRS 23

@[expose] noncomputable def QM (l : Nat) : Nat := getL CFSG.KC.Co1B.oneK IRS (36 + l)

@[expose] noncomputable def RK (i : Nat) : Nat :=
  QT.P (bfsPosK QT.P QT.S QT.N (CFSG.Sporadic.Co1.InvNative.rowsKey (twoARoots.getD i #[])))

@[expose] noncomputable def GM (i l : Nat) : Nat := D2.M ((twoACGens.getD i []).getD l 0)

@[expose] noncomputable def GIM (i l : Nat) : Nat := D2.MI ((twoACGens.getD i []).getD l 0)

theorem kb : (Nat.beq (D1.M 0) SA && Nat.beq (D1.M 1) SB && Nat.beq (D1.M 2) IA) = true := by
  quickRfl
theorem kD1 : dagIK D1.M D1.MI 3 D1.N twoAD1 = true := by quickRfl
theorem kI : twoABray.all (fun j => decide (3 < j) && decide (j ≤ D1.N)) = true := by quickRfl
theorem kBind : bindK D1.M D2.M twoABray = true := by quickRfl
theorem kD2 : dagIK D2.M D2.MI twoABray.length D2.N twoAD2 = true := by quickRfl
theorem kC : commK D1.M IA twoABray = true := by quickRfl
theorem kN : (Nat.beq D2.N 35 && Nat.beq QT.N 512) = true := by quickRfl

theorem f0 : fixesK D2.M (twoAVGens.getD 0 []) twoAVBase 0 = true := by quickRfl
theorem f1 : fixesK D2.M (twoAVGens.getD 1 []) twoAVBase 1 = true := by quickRfl
theorem f2 : fixesK D2.M (twoAVGens.getD 2 []) twoAVBase 2 = true := by quickRfl
theorem f3 : fixesK D2.M (twoAVGens.getD 3 []) twoAVBase 3 = true := by quickRfl
theorem f4 : fixesK D2.M (twoAVGens.getD 4 []) twoAVBase 4 = true := by quickRfl
theorem f5 : fixesK D2.M (twoAVGens.getD 5 []) twoAVBase 5 = true := by quickRfl

theorem kQ : gtPinK QM 8 512 QT.N QT.P QT.PAR QT.LAB QT.W QT.S = true := by quickRfl

theorem kR : allN 8 (fun i => strictB (bfsPosK QT.P QT.S QT.N
    (CFSG.Sporadic.Co1.InvNative.rowsKey (twoARoots.getD i #[]))) fun w =>
      bAnd(Nat.blt w QT.N, unpack 24 24 (QT.P w) == twoARoots.getD i #[])) = true := by
  quickRfl

@[expose] noncomputable def levelK (i : Nat) (P PAR LAB W S : Nat → Nat) (N : Nat) : Bool :=
  bAnd((twoACGens.getD i []).all (fun j => decide (j < 35)),
  bAnd(allN (twoACGens.getD i []).length (fun l => bAnd(invOKK (GM i l) (GIM i l),
    allN i fun k => Nat.beq (mulWK (GM i l) (RK k)) (mulWK (RK k) (GM i l)))),
    ctPinK (GM i) (GIM i) (RK i) (twoACGens.getD i []).length (twoACSizes.getD i 0) N P PAR LAB W S))

theorem kL0 : levelK 0 CT.L0.P CT.L0.PAR CT.L0.LAB CT.L0.W CT.L0.S CT.L0.N = true := by quickRfl
theorem kL1 : levelK 1 CT.L1.P CT.L1.PAR CT.L1.LAB CT.L1.W CT.L1.S CT.L1.N = true := by quickRfl
theorem kL2 : levelK 2 CT.L2.P CT.L2.PAR CT.L2.LAB CT.L2.W CT.L2.S CT.L2.N = true := by quickRfl
theorem kL3 : levelK 3 CT.L3.P CT.L3.PAR CT.L3.LAB CT.L3.W CT.L3.S CT.L3.N = true := by quickRfl
theorem kL4 : levelK 4 CT.L4.P CT.L4.PAR CT.L4.LAB CT.L4.W CT.L4.S CT.L4.N = true := by quickRfl
theorem kL5 : levelK 5 CT.L5.P CT.L5.PAR CT.L5.LAB CT.L5.W CT.L5.S CT.L5.N = true := by quickRfl
theorem kL6 : levelK 6 CT.L6.P CT.L6.PAR CT.L6.LAB CT.L6.W CT.L6.S CT.L6.N = true := by quickRfl
theorem kL7 : levelK 7 CT.L7.P CT.L7.PAR CT.L7.LAB CT.L7.W CT.L7.S CT.L7.N = true := by quickRfl

theorem kB : allN 8 (fun i => bAnd(invOKK (D2.M i) (D2.MI i), allN 8 fun l =>
    bfsMemK QT.P QT.S QT.N (mulWK (mulWK (D2.M i) (QM l)) (D2.MI i)))) = true := by
  quickRfl

@[expose] def FA : List Nat := [1071, 634, 2156, 296, 144, 6176, 11456, 95360, 34560, 227840,
  2147328, 739328, 413696, 6529024, 1458176, 10354688]

@[expose] def YA : List Nat := [1, 3, 5, 8, 29, 37, 100, 16403]

theorem kM : (bfsMemK QT.P QT.S QT.N IA &&
    allN 8 (fun l => Nat.beq (mulWK (QM l) IA) (mulWK IA (QM l))) &&
    fixK 24 TA 0 FA YA 16 65536 0 && Nat.beq (mulWK IA IA) idM &&
    (unpack 24 24 IA != unpack 24 24 idM)) = true := by
  quickRfl

end CertificateChecks.KernelCo1B.C2044

end
