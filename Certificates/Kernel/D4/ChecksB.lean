module

public import Certificates.Kernel.D4.Tabs
public import Certificates.Kernel.D4.ChainBD
public import Certificates.Kernel.D4.EnumB
public import Certificates.Kernel.D4.OrbB
public import Certificates.Kernel.SporSch.Ru.RowsGen
public import Certificates.Data.Kernel.D4K
public import Certificates.Data.Kernel.Misc.ChainTail
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelD4

open CFSG.RankThree.PartTwo.Sec4.Item434D42 CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.B3S3K
open CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ChainTail CFSG.KC.D4K

theorem sB : allN 9 (fun j => Nat.beq (CB.S j) (HX.F (Nat.add 77 j))) = true := by quickRfl

theorem permB' : allN 9 (fun j => permOK 2457 12 (mask 12) (2457 * 12) (CB.S j) (CB.SI j)) =
    true := by quickRfl

theorem abB : Nat.beq (HX.F 77) (HX.F 66) = true ∧ Nat.beq (HX.F 78) (HX.F 67) = true :=
  ⟨by quickRfl, by quickRfl⟩

theorem rc0B : Nat.beq (rcnt (CB.LR 0)) 2457 = true := by quickRfl

theorem baseB : ∀ t < 5, d4ChainBBaseArr[t]! = pg 12 (mask 12) CB.BP t := by decide +kernel

theorem orbB : ((List.range 5).map fun i => rcnt (CB.LR i)) = [2457, 2048, 21, 2, 1] := by
  decide +kernel

theorem wB : CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 9 dB = d4ChainBWords := by
  decide +kernel

theorem ndB : d4ChainBBaseArr.toList.Nodup := by decide +kernel

theorem bGB : allN 5 (fun j => Nat.beq (EB.G j) (HX.F (Nat.add 86 j))) = true ∧
    Nat.beq EB.ng 5 = true ∧ Nat.beq EB.N 648 = true := ⟨by quickRfl, by quickRfl, by quickRfl⟩

theorem siftGB : allN 5 (fun k => siftOK 2457 12 CB.LR CB.TRI CB.BP 5 (EB.G k)) = true := by
  quickRfl

theorem relsB : relsK 2457 12 3 CB.BP (LX 1) 5 d4RelsB = true := by quickRfl

theorem commB : commK 2457 12 5 (LX 1) EB.G = true := by quickRfl

theorem x1 : permB 2457 12 (LX 1) = true := by quickRfl

@[expose] noncomputable def tailB (k : Nat) : Bool :=
  ptailBranchK 2457 12 CB.LR CB.TR CB.BP (LX 1) (pw 2457 12 (LX 1)) d4RelsB EB.N EB.T 5 k

theorem tbR0 : tailB (RB 0) = true := by quickRfl

theorem tbR1 : tailB (RB 1) = true := by quickRfl

theorem tbR2 : tailB (RB 2) = true := by quickRfl

theorem tbR3 : tailB (RB 3) = true := by quickRfl

theorem tbR4 : tailB (RB 4) = true := by quickRfl

theorem tbR5 : tailB (RB 5) = true := by quickRfl

theorem tbR6 : tailB (RB 6) = true := by quickRfl

theorem kOrbB : allN 2457 orbKB = true := by quickRfl

end CertificateChecks.KernelD4

end
