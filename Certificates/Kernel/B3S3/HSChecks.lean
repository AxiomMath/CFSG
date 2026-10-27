module

public import Certificates.Kernel.B3S3.HSEnum
public import Certificates.Data.Kernel.B3S3K
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelB3S3.HS

open CFSG.HardMathSupport.Solomon.Coordinator.B3S3 CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.KC.Misc.ArrEnum CFSG.KC.B3S3K

theorem szOK' : szOK 3850 12 = true := by quickRfl

theorem bS : ∀ j < 11, Nat.beq (C0.S j) (SS.F j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem perm0 : allN 11 (fun j => permOK 3850 12 (mask 12) (3850 * 12) (C0.S j) (C0.SI j)) =
    true := by
  quickRfl

theorem bget0 : ∀ t < 6, hsS3C0Base[t]! = pg 12 (mask 12) C0.BP t := by decide +kernel

theorem lines : linesK 3850 12 3 EQ.N 4 EQ.T LX.F = true := by quickRfl

theorem trans : transK 3850 12 4 H.F XC.F LX.F hsS3Rec = true := by quickRfl

theorem siftQ : ∀ k < 2, Nat.beq (Nat.shiftRight (QG.F k) (3850 * 12)) 0 = true ∧
    allN 3850 (fun t => Nat.blt (pg 12 (mask 12) (QG.F k) t) 3850) = true ∧
    siftK 3850 12 (mask 12) (3850 * 12) (pidn 3850 12) C0.LR C0.TRI C0.BP 6 0 (QG.F k) = true := by
  intro k hk
  interval_cases k <;> exact ⟨by quickRfl, by quickRfl, by quickRfl⟩

theorem siftH : ∀ k < 4, Nat.beq (Nat.shiftRight (H.F k) (3850 * 12)) 0 = true ∧
    allN 3850 (fun t => Nat.blt (pg 12 (mask 12) (H.F k) t) 3850) = true ∧
    siftK 3850 12 (mask 12) (3850 * 12) (pidn 3850 12) C0.LR C0.TRI C0.BP 6 0 (H.F k) = true := by
  intro k hk
  interval_cases k <;> exact ⟨by quickRfl, by quickRfl, by quickRfl⟩

theorem siftG : ∀ k < 4, Nat.beq (Nat.shiftRight (E0.G k) (3850 * 12)) 0 = true ∧
    allN 3850 (fun t => Nat.blt (pg 12 (mask 12) (E0.G k) t) 3850) = true ∧
    siftK 3850 12 (mask 12) (3850 * 12) (pidn 3850 12) C0.LR C0.TRI C0.BP 6 0 (E0.G k) = true := by
  intro k hk
  interval_cases k <;> exact ⟨by quickRfl, by quickRfl, by quickRfl⟩

theorem rels0 : relsK 3850 12 3 C0.BP (XC.F 0) 6 hsS3C0Rels = true := by quickRfl

theorem comm0 : commK 3850 12 4 (XC.F 0) E0.G = true := by quickRfl

theorem x0 : permB 3850 12 (XC.F 0) = true ∧
    Nat.beq (pw 3850 12 (XC.F 0) 3) (pidn 3850 12) = true := ⟨by quickRfl, by quickRfl⟩

theorem rc0 : Nat.beq (rcnt (C0.LR 0)) 3850 = true := by quickRfl

theorem orb0 : Nat.beq (((List.range 6).map fun i => rcnt (C0.LR i)).prod) 44352000 = true := by
  quickRfl

theorem pL : allN 4 (fun j => permB 3850 12 (LX.F j)) = true := by quickRfl

theorem pQ : allN 2 (fun j => permB 3850 12 (QG.F j)) = true := by quickRfl

theorem nT : Nat.beq QG.N 2 = true ∧ Nat.beq LX.N 4 = true ∧ Nat.beq H.N 4 = true ∧
    Nat.beq XC.N 1 = true ∧ Nat.beq SS.N 11 = true ∧ Nat.beq GG.N 4 = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

end CertificateChecks.KernelB3S3.HS

end
