module

public import Certificates.Data.B3Spor3.M24
public import Certificates.Data.Kernel.B3S3K
public import Certificates.Data.Kernel.Misc.ChainTail
public import Certificates.Kernel.B3S3.Gen
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.SporSch.Th.GenV4
public meta import Certificates.Data.B3Spor3.M24
public meta import Certificates.Kernel.B3S3.Gen
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelB3S3.M24

open CFSG.HardMathSupport.Solomon.Coordinator.B3S3

@[expose] def d0 : List (List ℤ) := m24S3C0W.toList.drop 2

@[expose] def d1 : List (List ℤ) := m24S3C1W.toList.drop 2

meta def ab : Array (Array Nat) := #[m24S3A, m24S3B]

meta def pts0 : Array (Array Nat) := (CFSG.KC.BfsGen.search 24 5 m24S3C0Gens).1

meta def pts1 : Array (Array Nat) := (CFSG.KC.BfsGen.search 24 5 m24S3C1Gens).1

meta def w0 : List Nat × List Nat := CFSG.KC.B3S3Gen.convWit 24 pts0 [2, 5] [1, 2, 5]

meta def w1 : List Nat × List Nat := CFSG.KC.B3S3Gen.convWit 24 pts1 [2, 7] [1]

meta def wj0 : List Nat := w0.1

meta def wr0 : List Nat := w0.2

meta def wj1 : List Nat := w1.1

meta def wr1 : List Nat := w1.2

end CertificateChecks.KernelB3S3.M24

end

#ks_rawchain CertificateChecks.KernelB3S3.M24.C0 24 5 24
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m24S3C0S
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m24S3C0Base 2 CertificateChecks.KernelB3S3.M24.d0
#ks_rawchain CertificateChecks.KernelB3S3.M24.C1 24 5 24
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m24S3C1S
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m24S3C1Base 2 CertificateChecks.KernelB3S3.M24.d1
#kmisc_packarrs CertificateChecks.KernelB3S3.M24.AB CertificateChecks.KernelB3S3.M24.ab 5
#kmisc_packarrs CertificateChecks.KernelB3S3.M24.QG
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m24S3QGens 5
#kmisc_packarrs CertificateChecks.KernelB3S3.M24.LX
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m24S3Lines 5
#kmisc_packarrs CertificateChecks.KernelB3S3.M24.H
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m24S3Trans 5
#kmisc_packarrs CertificateChecks.KernelB3S3.M24.XC
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m24S3CaseX 5
#kb3_enum CertificateChecks.KernelB3S3.M24.EQ
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m24S3QGens
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m24S3C0Base 24 5
#kb3_enum CertificateChecks.KernelB3S3.M24.E0
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m24S3C0Gens
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m24S3C0Base 24 5
#kb3_enum CertificateChecks.KernelB3S3.M24.E1
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m24S3C1Gens
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m24S3C1Base 24 5
#kss_natlist CertificateChecks.KernelB3S3.M24.WJ0 CertificateChecks.KernelB3S3.M24.wj0
#kss_natlist CertificateChecks.KernelB3S3.M24.WR0 CertificateChecks.KernelB3S3.M24.wr0
#kss_natlist CertificateChecks.KernelB3S3.M24.WJ1 CertificateChecks.KernelB3S3.M24.wj1
#kss_natlist CertificateChecks.KernelB3S3.M24.WR1 CertificateChecks.KernelB3S3.M24.wr1

public section

namespace CertificateChecks.KernelB3S3.M24

open CFSG.HardMathSupport.Solomon.Coordinator.B3S3 CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ChainTail CFSG.KC.B3S3K

theorem szOK' : szOK 24 5 = true := by quickRfl

theorem bA : arrBind m24S3A 24 5 (AB 0) = true := by quickRfl

theorem bB : arrBind m24S3B 24 5 (AB 1) = true := by quickRfl

theorem pAB : permB 24 5 (AB 0) = true ∧ permB 24 5 (AB 1) = true := ⟨by quickRfl, by quickRfl⟩

theorem bS0 : ∀ j < 13, arrBind m24S3C0S[j]! 24 5 (C0.S j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem bS1 : ∀ j < 12, arrBind m24S3C1S[j]! 24 5 (C1.S j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem bQ : ∀ j < 2, arrBind m24S3QGens[j]! 24 5 (QG j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem bL : ∀ j < 13, arrBind m24S3Lines[j]! 24 5 (LX j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem bH : ∀ j < 13, arrBind m24S3Trans[j]! 24 5 (H j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem bX : ∀ j < 2, arrBind m24S3CaseX[j]! 24 5 (XC j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem bG0 : ∀ j < 4, arrBind m24S3C0Gens[j]! 24 5 (E0.G j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem bG1 : ∀ j < 4, arrBind m24S3C1Gens[j]! 24 5 (E1.G j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem bQE : ∀ j < 2, Nat.beq (EQ.G j) (QG j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem perm0 : allN 13 (fun j => permOK 24 5 (mask 5) (24 * 5) (C0.S j) (C0.SI j)) = true := by
  quickRfl

theorem perm1 : allN 12 (fun j => permOK 24 5 (mask 5) (24 * 5) (C1.S j) (C1.SI j)) = true := by
  quickRfl

theorem head0 : Nat.beq (C0.S 0) (AB 0) = true ∧ Nat.beq (C0.S 1) (AB 1) = true :=
  ⟨by quickRfl, by quickRfl⟩

theorem head1 : Nat.beq (C1.S 0) (AB 0) = true ∧ Nat.beq (C1.S 1) (AB 1) = true :=
  ⟨by quickRfl, by quickRfl⟩

theorem bget0 : ∀ t < 24, m24S3C0Base[t]! = pg 5 (mask 5) C0.BP t := by decide +kernel

theorem bget1 : ∀ t < 24, m24S3C1Base[t]! = pg 5 (mask 5) C1.BP t := by decide +kernel

theorem lines : linesK 24 5 3 EQ.N 13 EQ.T LX = true := by quickRfl

theorem trans : transK 24 5 13 H XC LX m24S3Rec = true := by quickRfl

theorem siftQ : ∀ k < 2, Nat.beq (Nat.shiftRight (QG k) (24 * 5)) 0 = true ∧
    allN 24 (fun t => Nat.blt (pg 5 (mask 5) (QG k) t) 24) = true ∧
    siftK 24 5 (mask 5) (24 * 5) (pidn 24 5) C0.LR C0.TRI C0.BP 24 0 (QG k) = true := by
  intro k hk
  interval_cases k <;> exact ⟨by quickRfl, by quickRfl, by quickRfl⟩

theorem siftH : ∀ k < 13, Nat.beq (Nat.shiftRight (H k) (24 * 5)) 0 = true ∧
    allN 24 (fun t => Nat.blt (pg 5 (mask 5) (H k) t) 24) = true ∧
    siftK 24 5 (mask 5) (24 * 5) (pidn 24 5) C0.LR C0.TRI C0.BP 24 0 (H k) = true := by
  intro k hk
  interval_cases k <;> exact ⟨by quickRfl, by quickRfl, by quickRfl⟩

theorem siftG0 : ∀ k < 4, Nat.beq (Nat.shiftRight (E0.G k) (24 * 5)) 0 = true ∧
    allN 24 (fun t => Nat.blt (pg 5 (mask 5) (E0.G k) t) 24) = true ∧
    siftK 24 5 (mask 5) (24 * 5) (pidn 24 5) C0.LR C0.TRI C0.BP 24 0 (E0.G k) = true := by
  intro k hk
  interval_cases k <;> exact ⟨by quickRfl, by quickRfl, by quickRfl⟩

theorem siftG1 : ∀ k < 4, Nat.beq (Nat.shiftRight (E1.G k) (24 * 5)) 0 = true ∧
    allN 24 (fun t => Nat.blt (pg 5 (mask 5) (E1.G k) t) 24) = true ∧
    siftK 24 5 (mask 5) (24 * 5) (pidn 24 5) C1.LR C1.TRI C1.BP 24 0 (E1.G k) = true := by
  intro k hk
  interval_cases k <;> exact ⟨by quickRfl, by quickRfl, by quickRfl⟩

theorem rels0 : relsK 24 5 3 C0.BP (XC 0) 24 m24S3C0Rels = true := by quickRfl

theorem rels1 : relsK 24 5 3 C1.BP (XC 1) 24 m24S3C1Rels = true := by quickRfl

theorem comm0 : commK 24 5 4 (XC 0) E0.G = true := by quickRfl

theorem comm1 : commK 24 5 4 (XC 1) E1.G = true := by quickRfl

theorem x0 : permB 24 5 (XC 0) = true ∧ Nat.beq (pw 24 5 (XC 0) 3) (pidn 24 5) = true :=
  ⟨by quickRfl, by quickRfl⟩

theorem x1 : permB 24 5 (XC 1) = true ∧ Nat.beq (pw 24 5 (XC 1) 3) (pidn 24 5) = true :=
  ⟨by quickRfl, by quickRfl⟩

theorem rc0 : Nat.beq (rcnt (C0.LR 0)) 24 = true := by quickRfl

theorem rc1 : Nat.beq (rcnt (C1.LR 0)) 24 = true := by quickRfl

theorem tail0 : allN 24 (ptailBranchK 24 5 C0.LR C0.TR C0.BP (XC 0) (pw 24 5 (XC 0))
    m24S3C0Rels E0.N E0.T 24) = true := by quickRfl

theorem tail1 : allN 24 (ptailBranchK 24 5 C1.LR C1.TR C1.BP (XC 1) (pw 24 5 (XC 1))
    m24S3C1Rels E1.N E1.T 24) = true := by quickRfl

theorem conv0 : allN E0.N (convAt 24 5 E0.N E0.T [2, 5] [1, 2, 5] WJ0 WR0) = true := by quickRfl

theorem conv1 : allN E1.N (convAt 24 5 E1.N E1.T [2, 7] [1] WJ1 WR1) = true := by quickRfl

theorem orb0 : Nat.beq (((List.range 24).map fun i => rcnt (C0.LR i)).prod) 244823040 = true := by
  quickRfl

theorem pL : allN 13 (fun j => permB 24 5 (LX j)) = true := by quickRfl

theorem pQ : allN 2 (fun j => permB 24 5 (QG j)) = true := by quickRfl

theorem n0 : Nat.beq EQ.N 27 = true ∧ Nat.beq E0.N 1080 = true ∧ Nat.beq E0.ng 4 = true ∧
    Nat.beq EQ.ng 2 = true ∧ Nat.beq E1.N 504 = true ∧ Nat.beq E1.ng 4 = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

end CertificateChecks.KernelB3S3.M24

end
