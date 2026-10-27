module

public import Certificates.Kernel.D4.Tabs
public import Certificates.Kernel.D4.ChainAD
public import Certificates.Kernel.D4.EnumQ
public import Certificates.Kernel.D4.EnumA
public import Certificates.Kernel.SporSch.Ru.RowsGen
public import Certificates.Data.Kernel.D4K
public import Certificates.Data.Kernel.Misc.ChainTail
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelD4

open CFSG.RankThree.PartTwo.Sec4.Item434D42 CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.B3S3K
open CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ChainTail CFSG.KC.D4K

theorem szOK' : szOK 2457 12 = true := by quickRfl

theorem sA : allN 8 (fun j => Nat.beq (CA.S j) (HX.F (Nat.add 66 j))) = true := by quickRfl

theorem permA : allN 8 (fun j => permOK 2457 12 (mask 12) (2457 * 12) (CA.S j) (CA.SI j)) =
    true := by quickRfl

theorem baseA : ∀ t < 7, d4ChainABaseArr[t]! = pg 12 (mask 12) CA.BP t := by decide +kernel

theorem orbA : ((List.range 7).map fun i => rcnt (CA.LR i)) = [2457, 2048, 7, 1, 1, 3, 2] := by
  decide +kernel

theorem wA : CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 8 dA = d4ChainAWords := by
  decide +kernel

theorem ndA : d4ChainABaseArr.toList.Nodup := by decide +kernel

theorem nsA : 2457 ≤ CA.NS * 16 := by decide +kernel

theorem bQ : allN 4 (fun j => Nat.beq (EQ.G j) (HX.F j)) = true ∧ Nat.beq EQ.ng 4 = true ∧
    Nat.beq EQ.N 81 = true := ⟨by quickRfl, by quickRfl, by quickRfl⟩

theorem pQ : allN 4 (fun j => permB 2457 12 (EQ.G j)) = true := by quickRfl

theorem rc0A : Nat.beq (rcnt (CA.LR 0)) 2457 = true := by quickRfl

theorem siftQ : allN 4 (fun k => siftOK 2457 12 CA.LR CA.TRI CA.BP 7 (HX.F k)) = true := by
  quickRfl

@[expose] noncomputable def linesSl (s : Nat) : Bool :=
  allBlk (Nat.mul 9 s) (lineAt 2457 12 3 31 EQ.T LX) 9

end CertificateChecks.KernelD4

end

#kss_each CertificateChecks.KernelD4.LS CertificateChecks.KernelD4.linesSl 9

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelD4

open CFSG.RankThree.PartTwo.Sec4.Item434D42 CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.B3S3K
open CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ChainTail CFSG.KC.D4K

theorem pL : allN 31 (fun j => permB 2457 12 (LX j) && Nat.beq (pw 2457 12 (LX j) 3)
    (pidn 2457 12)) = true := by quickRfl

theorem trans : transK 2457 12 31 HT LX LX d4Rec = true := by quickRfl

theorem siftH : allN 31 (fun k => siftOK 2457 12 CA.LR CA.TRI CA.BP 7 (HT k)) = true := by
  quickRfl

theorem bG : allN 3 (fun j => Nat.beq (EA.G j) (HX.F (Nat.add 74 j))) = true ∧
    Nat.beq EA.ng 3 = true ∧ Nat.beq EA.N 1512 = true := ⟨by quickRfl, by quickRfl, by quickRfl⟩

theorem siftG : allN 3 (fun k => siftOK 2457 12 CA.LR CA.TRI CA.BP 7 (EA.G k)) = true := by
  quickRfl

theorem relsA : relsK 2457 12 3 CA.BP (LX 0) 7 d4RelsA = true := by quickRfl

theorem commA : commK 2457 12 3 (LX 0) EA.G = true := by quickRfl

theorem x0 : permB 2457 12 (LX 0) = true := by quickRfl

end CertificateChecks.KernelD4

end
