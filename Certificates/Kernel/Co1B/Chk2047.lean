module

public import Certificates.Kernel.Co1B.Tow2047
public import Certificates.Kernel.Co1B.Bfs2047
public import Certificates.Kernel.Co1B.IotaData
public import Certificates.Data.Kernel.SporSch.Co1Cent
public import Certificates.Data.Kernel.SporSch.Co1Bfs
public import Certificates.Data.Kernel.SporSch.Co1Stab
public import Certificates.Data.CFSGNative.Co1.Involutions
public import Certificates.Data.Kernel.Co1F2
public import Certificates.Data.Kernel.Co1B
public import Certificates.Data.Kernel.Co1BW
public import CFSG.Sporadic.Co1Block.TwoCData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.C2047

open CFSG.KC.Enum CFSG.KS.SporSch.M24 CFSG.KS.SporSch.VOrb CFSG.KC.Co1F2 CFSG.KD.Co1B
  CFSG.Sporadic.Co1Block CFSG.KS.Raw
open CFSG.KC.Co1B (mulWK)

@[expose] noncomputable def IC : Nat := getL CFSG.KC.Co1B.oneK IRS 51

@[expose] noncomputable def QM (l : Nat) : Nat := D2.M (twoCQGens.getD l 0)

@[expose] noncomputable def RK (i : Nat) : Nat :=
  QT.P (bfsPosK QT.P QT.S QT.N (CFSG.Sporadic.Co1.InvNative.rowsKey (twoCRoots.getD i #[])))

@[expose] noncomputable def GM (i l : Nat) : Nat := D2.M ((twoCCGens.getD i []).getD l 0)

@[expose] noncomputable def GIM (i l : Nat) : Nat := D2.MI ((twoCCGens.getD i []).getD l 0)

theorem kb : (Nat.beq (D1.M 0) SA && Nat.beq (D1.M 1) SB && Nat.beq (D1.M 2) IC) = true := by
  quickRfl
theorem kD1 : dagIK D1.M D1.MI 3 D1.N twoCD1 = true := by quickRfl
theorem kI : twoCBray.all (fun j => decide (3 < j) && decide (j ≤ D1.N)) = true := by quickRfl
theorem kBind : bindK D1.M D2.M twoCBray = true := by quickRfl
theorem kD2 : dagIK D2.M D2.MI twoCBray.length D2.N twoCD2 = true := by quickRfl
theorem kC : commK D1.M IC twoCBray = true := by quickRfl
theorem kN : (Nat.beq D2.N 42 && Nat.beq QT.N 2048 && twoCQGens.all (fun j => decide (j < 42))) =
    true := by
  quickRfl

theorem f0 : fixesK D2.M (twoCVGens.getD 0 []) twoCVBase 0 = true := by quickRfl
theorem f1 : fixesK D2.M (twoCVGens.getD 1 []) twoCVBase 1 = true := by quickRfl
theorem f2 : fixesK D2.M (twoCVGens.getD 2 []) twoCVBase 2 = true := by quickRfl
theorem f3 : fixesK D2.M (twoCVGens.getD 3 []) twoCVBase 3 = true := by quickRfl
theorem f4 : fixesK D2.M (twoCVGens.getD 4 []) twoCVBase 4 = true := by quickRfl
theorem f5 : fixesK D2.M (twoCVGens.getD 5 []) twoCVBase 5 = true := by quickRfl
theorem f6 : fixesK D2.M (twoCVGens.getD 6 []) twoCVBase 6 = true := by quickRfl
theorem f7 : fixesK D2.M (twoCVGens.getD 7 []) twoCVBase 7 = true := by quickRfl
theorem f8 : fixesK D2.M (twoCVGens.getD 8 []) twoCVBase 8 = true := by quickRfl
theorem f9 : fixesK D2.M (twoCVGens.getD 9 []) twoCVBase 9 = true := by quickRfl
theorem f10 : fixesK D2.M (twoCVGens.getD 10 []) twoCVBase 10 = true := by quickRfl

theorem kQ : gtPinK QM 11 2048 QT.N QT.P QT.PAR QT.LAB QT.W QT.S = true := by quickRfl

theorem kR : allN 3 (fun i => strictB (bfsPosK QT.P QT.S QT.N
    (CFSG.Sporadic.Co1.InvNative.rowsKey (twoCRoots.getD i #[]))) fun w =>
      bAnd(Nat.blt w QT.N, unpack 24 24 (QT.P w) == twoCRoots.getD i #[])) = true := by
  quickRfl

@[expose] noncomputable def levelK (i : Nat) (P PAR LAB W S : Nat → Nat) (N : Nat) : Bool :=
  bAnd((twoCCGens.getD i []).all (fun j => decide (j < 42)),
  bAnd(allN (twoCCGens.getD i []).length (fun l => bAnd(invOKK (GM i l) (GIM i l),
    allN i fun k => Nat.beq (mulWK (GM i l) (RK k)) (mulWK (RK k) (GM i l)))),
    ctPinK (GM i) (GIM i) (RK i) (twoCCGens.getD i []).length (twoCCSizes.getD i 0) N P PAR LAB W S))

theorem kL0 : levelK 0 CT.L0.P CT.L0.PAR CT.L0.LAB CT.L0.W CT.L0.S CT.L0.N = true := by quickRfl
theorem kL1 : levelK 1 CT.L1.P CT.L1.PAR CT.L1.LAB CT.L1.W CT.L1.S CT.L1.N = true := by quickRfl
theorem kL2 : levelK 2 CT.L2.P CT.L2.PAR CT.L2.LAB CT.L2.W CT.L2.S CT.L2.N = true := by quickRfl

theorem kB : allN 8 (fun i => bAnd(invOKK (D2.M i) (D2.MI i), allN 11 fun l =>
    bfsMemK QT.P QT.S QT.N (mulWK (mulWK (D2.M i) (QM l)) (D2.MI i)))) = true := by
  quickRfl

theorem kM : (allN 11 (fun l => Nat.beq (mulWK (QM l) IC) (mulWK IC (QM l))) &&
    allN 11 (fun l => Nat.beq (mulWK (QM l) (QM l)) idM) &&
    allN 11 (fun l => allN 11 fun l' => Nat.beq (mulWK (QM l) (QM l')) (mulWK (QM l') (QM l))) &&
    Nat.beq (mulWK IC IC) idM && (unpack 24 24 IC != unpack 24 24 idM)) = true := by
  quickRfl

end CertificateChecks.KernelCo1B.C2047

end
