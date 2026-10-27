module

public import Certificates.Data.B3Spor3.J2
public import Certificates.Data.Kernel.B3S3K
public import Certificates.Data.Kernel.Misc.ChainTail
public import Certificates.Kernel.B3S3.Gen
public import Certificates.Kernel.GFR3.J2
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.SporSch.Th.GenV4
public meta import Certificates.Data.B3Spor3.J2
public meta import Certificates.Kernel.B3S3.Gen
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelB3S3.J2

open CFSG.HardMathSupport.Solomon.Coordinator.B3S3 CFSG.HardMathSupport.Solomon.Coordinator

@[expose] def d1 : List (List ℤ) := j2S3C1W.toList.drop 2

meta def xc : Array (Array Nat) := j2S3Data.caseX

meta def pts0 : Array (Array Nat) := (CFSG.KC.BfsGen.search 315 9 j2ThreeGens).1

meta def w0 : List Nat × List Nat := CFSG.KC.B3S3Gen.convWit 315 pts0 [2, 5] [1, 2, 5]

meta def wj0 : List Nat := w0.1

meta def wr0 : List Nat := w0.2

end CertificateChecks.KernelB3S3.J2

end

#ks_rawchain CertificateChecks.KernelB3S3.J2.C1 315 9 63
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.j2S3C1S
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.j2S3C1Base 2 CertificateChecks.KernelB3S3.J2.d1
#kmisc_packarrs CertificateChecks.KernelB3S3.J2.QG
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.j2S3QGens 9
#kmisc_packarrs CertificateChecks.KernelB3S3.J2.LX
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.j2S3Lines 9
#kmisc_packarrs CertificateChecks.KernelB3S3.J2.H
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.j2S3Trans 9
#kmisc_packarrs CertificateChecks.KernelB3S3.J2.XC CertificateChecks.KernelB3S3.J2.xc 9
#kb3_enum CertificateChecks.KernelB3S3.J2.EQ
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.j2S3QGens
  CFSG.HardMathSupport.Solomon.Coordinator.j2ThreeBaseArr 315 9
#kb3_enum CertificateChecks.KernelB3S3.J2.E1
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.j2S3C1Gens
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.j2S3C1Base 315 9
#kss_natlist CertificateChecks.KernelB3S3.J2.WJ0 CertificateChecks.KernelB3S3.J2.wj0
#kss_natlist CertificateChecks.KernelB3S3.J2.WR0 CertificateChecks.KernelB3S3.J2.wr0

public section

namespace CertificateChecks.KernelB3S3.J2

open CFSG.HardMathSupport.Solomon.Coordinator.B3S3 CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ChainTail CFSG.KC.B3S3K

theorem bS1 : ∀ j < 9, arrBind j2S3C1S[j]! 315 9 (C1.S j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem bQ : ∀ j < 3, arrBind j2S3QGens[j]! 315 9 (QG j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem bL : ∀ j < 13, arrBind j2S3Lines[j]! 315 9 (LX j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem bH : ∀ j < 13, arrBind j2S3Trans[j]! 315 9 (H j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem bX1 : arrBind j2S3X1 315 9 (XC 1) = true := by quickRfl

theorem bX0 : Nat.beq (XC 0) (KernelGFR3.J2.E.G 0) = true := by quickRfl

theorem bG1 : ∀ j < 3, arrBind j2S3C1Gens[j]! 315 9 (E1.G j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem bQE : ∀ j < 3, Nat.beq (EQ.G j) (QG j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem perm1 : allN 9 (fun j => permOK 315 9 (mask 9) (315 * 9) (C1.S j) (C1.SI j)) = true := by
  quickRfl

theorem head1 : Nat.beq (C1.S 0) (KernelGFR3.J2.JS.F 0) = true ∧ Nat.beq (C1.S 1) (KernelGFR3.J2.JS.F 1) = true :=
  ⟨by quickRfl, by quickRfl⟩

theorem bget1 : ∀ t < 5, j2S3C1Base[t]! = pg 9 (mask 9) C1.BP t := by decide +kernel

theorem lines : linesK 315 9 3 EQ.N 13 EQ.T LX = true := by quickRfl

theorem trans : transK 315 9 13 H XC LX j2S3Rec = true := by quickRfl

theorem siftQ : ∀ k < 3, Nat.beq (Nat.shiftRight (QG k) (315 * 9)) 0 = true ∧
    allN 315 (fun t => Nat.blt (pg 9 (mask 9) (QG k) t) 315) = true ∧
    siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) KernelGFR3.J2.C.LR KernelGFR3.J2.C.TRI KernelGFR3.J2.C.BP 7 0 (QG k) = true := by
  intro k hk
  interval_cases k <;> exact ⟨by quickRfl, by quickRfl, by quickRfl⟩

theorem siftH : ∀ k < 13, Nat.beq (Nat.shiftRight (H k) (315 * 9)) 0 = true ∧
    allN 315 (fun t => Nat.blt (pg 9 (mask 9) (H k) t) 315) = true ∧
    siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) KernelGFR3.J2.C.LR KernelGFR3.J2.C.TRI KernelGFR3.J2.C.BP 7 0 (H k) = true := by
  intro k hk
  interval_cases k <;> exact ⟨by quickRfl, by quickRfl, by quickRfl⟩

theorem siftG1 : ∀ k < 3, Nat.beq (Nat.shiftRight (E1.G k) (315 * 9)) 0 = true ∧
    allN 315 (fun t => Nat.blt (pg 9 (mask 9) (E1.G k) t) 315) = true ∧
    siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) C1.LR C1.TRI C1.BP 5 0 (E1.G k) = true := by
  intro k hk
  interval_cases k <;> exact ⟨by quickRfl, by quickRfl, by quickRfl⟩

theorem rels1 : relsK 315 9 3 C1.BP (XC 1) 5 j2S3C1Rels = true := by quickRfl

theorem comm1 : commK 315 9 3 (XC 1) E1.G = true := by quickRfl

theorem x1 : permB 315 9 (XC 1) = true ∧ Nat.beq (pw 315 9 (XC 1) 3) (pidn 315 9) = true :=
  ⟨by quickRfl, by quickRfl⟩

theorem rc1 : Nat.beq (rcnt (C1.LR 0)) 315 = true := by quickRfl

theorem tail1 : allN 315 (ptailBranchK 315 9 C1.LR C1.TR C1.BP (XC 1) (pw 315 9 (XC 1))
    j2S3C1Rels E1.N E1.T 5) = true := by quickRfl

theorem conv0 : allN KernelGFR3.J2.E.N (convAt 315 9 KernelGFR3.J2.E.N KernelGFR3.J2.E.T [2, 5]
    [1, 2, 5] WJ0 WR0) = true := by
  quickRfl

theorem pL : allN 13 (fun j => permB 315 9 (LX j)) = true := by quickRfl

theorem pQ : allN 3 (fun j => permB 315 9 (QG j)) = true := by quickRfl

theorem n0 : Nat.beq EQ.N 27 = true ∧ Nat.beq EQ.ng 3 = true ∧ Nat.beq E1.N 36 = true ∧
    Nat.beq E1.ng 3 = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

theorem ch13513NegLines : (!(linesK 315 9 3 EQ.N 13 EQ.T H)) = true := by quickRfl

theorem ch13513NegConv : (!(allN KernelGFR3.J2.E.N (convAt 315 9 KernelGFR3.J2.E.N KernelGFR3.J2.E.T
    [2, 5] [1, 2, 5] (fun i => Nat.add 1 (WJ0 i)) WR0))) = true := by
  quickRfl

theorem ch13513NegRels : (!(relsK 315 9 3 C1.BP (XC 0) 5 j2S3C1Rels)) = true := by quickRfl

end CertificateChecks.KernelB3S3.J2

end
