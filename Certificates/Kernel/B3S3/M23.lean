module

public import Certificates.Data.B3Spor3.M23
public import Certificates.Data.Kernel.B3S3K
public import Certificates.Data.Kernel.Misc.ChainTail
public import Certificates.Kernel.B3S3.Gen
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.SporSch.Th.GenV4
public meta import Certificates.Data.B3Spor3.M23
public meta import Certificates.Kernel.B3S3.Gen
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelB3S3.M23

open CFSG.HardMathSupport.Solomon.Coordinator.B3S3

@[expose] def d0 : List (List ℤ) := m23S3C0W.toList.drop 2

meta def ab : Array (Array Nat) := #[m23S3A, m23S3B]

meta def pts0 : Array (Array Nat) := (CFSG.KC.BfsGen.search 23 5 m23S3C0Gens).1

meta def wj : List Nat := (CFSG.KC.B3S3Gen.convWit 23 pts0 [2, 5] [1]).1

meta def wr : List Nat := (CFSG.KC.B3S3Gen.convWit 23 pts0 [2, 5] [1]).2

end CertificateChecks.KernelB3S3.M23

end

#ks_rawchain CertificateChecks.KernelB3S3.M23.C0 23 5 23
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m23S3C0S
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m23S3C0Base 2 CertificateChecks.KernelB3S3.M23.d0
#kmisc_packarrs CertificateChecks.KernelB3S3.M23.AB CertificateChecks.KernelB3S3.M23.ab 5
#kmisc_packarrs CertificateChecks.KernelB3S3.M23.QG
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m23S3QGens 5
#kmisc_packarrs CertificateChecks.KernelB3S3.M23.LX
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m23S3Lines 5
#kmisc_packarrs CertificateChecks.KernelB3S3.M23.H
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m23S3Trans 5
#kmisc_packarrs CertificateChecks.KernelB3S3.M23.XC
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m23S3CaseX 5
#kb3_enum CertificateChecks.KernelB3S3.M23.EQ
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m23S3QGens
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m23S3C0Base 23 5
#kb3_enum CertificateChecks.KernelB3S3.M23.E0
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m23S3C0Gens
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m23S3C0Base 23 5
#kss_natlist CertificateChecks.KernelB3S3.M23.WJ CertificateChecks.KernelB3S3.M23.wj
#kss_natlist CertificateChecks.KernelB3S3.M23.WR CertificateChecks.KernelB3S3.M23.wr

public section

namespace CertificateChecks.KernelB3S3.M23

open CFSG.HardMathSupport.Solomon.Coordinator.B3S3 CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ChainTail CFSG.KC.B3S3K

theorem szOK' : szOK 23 5 = true := by quickRfl

theorem bA : arrBind m23S3A 23 5 (AB 0) = true := by quickRfl

theorem bB : arrBind m23S3B 23 5 (AB 1) = true := by quickRfl

theorem pAB : permB 23 5 (AB 0) = true ∧ permB 23 5 (AB 1) = true := ⟨by quickRfl, by quickRfl⟩

theorem bS : ∀ j < 10, arrBind m23S3C0S[j]! 23 5 (C0.S j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem bQ : ∀ j < 2, arrBind m23S3QGens[j]! 23 5 (QG j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem bL : ∀ j < 4, arrBind m23S3Lines[j]! 23 5 (LX j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem bH : ∀ j < 4, arrBind m23S3Trans[j]! 23 5 (H j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem bX : arrBind m23S3CaseX[0]! 23 5 (XC 0) = true := by quickRfl

theorem bG : ∀ j < 4, arrBind m23S3C0Gens[j]! 23 5 (E0.G j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem bQE : ∀ j < 2, Nat.beq (EQ.G j) (QG j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem perm0 : allN 10 (fun j => permOK 23 5 (mask 5) (23 * 5) (C0.S j) (C0.SI j)) = true := by
  quickRfl

theorem head0 : Nat.beq (C0.S 0) (AB 0) = true ∧ Nat.beq (C0.S 1) (AB 1) = true :=
  ⟨by quickRfl, by quickRfl⟩

theorem bget0 : ∀ t < 23, m23S3C0Base[t]! = pg 5 (mask 5) C0.BP t := by decide +kernel

theorem lines : linesK 23 5 3 EQ.N 4 EQ.T LX = true := by quickRfl

theorem trans : transK 23 5 4 H XC LX m23S3Rec = true := by quickRfl

theorem siftQ : ∀ k < 2, Nat.beq (Nat.shiftRight (QG k) (23 * 5)) 0 = true ∧
    allN 23 (fun t => Nat.blt (pg 5 (mask 5) (QG k) t) 23) = true ∧
    siftK 23 5 (mask 5) (23 * 5) (pidn 23 5) C0.LR C0.TRI C0.BP 23 0 (QG k) = true := by
  intro k hk
  interval_cases k <;> exact ⟨by quickRfl, by quickRfl, by quickRfl⟩

theorem siftH : ∀ k < 4, Nat.beq (Nat.shiftRight (H k) (23 * 5)) 0 = true ∧
    allN 23 (fun t => Nat.blt (pg 5 (mask 5) (H k) t) 23) = true ∧
    siftK 23 5 (mask 5) (23 * 5) (pidn 23 5) C0.LR C0.TRI C0.BP 23 0 (H k) = true := by
  intro k hk
  interval_cases k <;> exact ⟨by quickRfl, by quickRfl, by quickRfl⟩

theorem siftG : ∀ k < 4, Nat.beq (Nat.shiftRight (E0.G k) (23 * 5)) 0 = true ∧
    allN 23 (fun t => Nat.blt (pg 5 (mask 5) (E0.G k) t) 23) = true ∧
    siftK 23 5 (mask 5) (23 * 5) (pidn 23 5) C0.LR C0.TRI C0.BP 23 0 (E0.G k) = true := by
  intro k hk
  interval_cases k <;> exact ⟨by quickRfl, by quickRfl, by quickRfl⟩

theorem rels0 : relsK 23 5 3 C0.BP (XC 0) 23 m23S3C0Rels = true := by quickRfl

theorem comm0 : commK 23 5 4 (XC 0) E0.G = true := by quickRfl

theorem x0 : permB 23 5 (XC 0) = true ∧ Nat.beq (pw 23 5 (XC 0) 3) (pidn 23 5) = true :=
  ⟨by quickRfl, by quickRfl⟩

theorem rc0 : Nat.beq (rcnt (C0.LR 0)) 23 = true := by quickRfl

theorem tail0 : allN 23 (ptailBranchK 23 5 C0.LR C0.TR C0.BP (XC 0) (pw 23 5 (XC 0))
    m23S3C0Rels E0.N E0.T 23) = true := by quickRfl

theorem conv0 : allN E0.N (convAt 23 5 E0.N E0.T [2, 5] [1] WJ WR) = true := by quickRfl

theorem orb0 : Nat.beq (((List.range 23).map fun i => rcnt (C0.LR i)).prod) 10200960 = true := by
  quickRfl

theorem pL : allN 4 (fun j => permB 23 5 (LX j)) = true := by quickRfl

theorem pQ : allN 2 (fun j => permB 23 5 (QG j)) = true := by quickRfl

theorem n0 : Nat.beq EQ.N 9 = true ∧ Nat.beq E0.N 180 = true ∧ Nat.beq E0.ng 4 = true ∧
    Nat.beq EQ.ng 2 = true := ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

end CertificateChecks.KernelB3S3.M23

end
