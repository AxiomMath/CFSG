module

public import Certificates.Data.B3Spor3.M12
public import Certificates.Data.Kernel.B3S3K
public import Certificates.Data.Kernel.Misc.ChainTail
public import Certificates.Kernel.B3S3.Gen
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.SporSch.Th.GenV4
public meta import Certificates.Data.B3Spor3.M12
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelB3S3.M12

open CFSG.HardMathSupport.Solomon.Coordinator.B3S3

@[expose] def d0 : List (List ℤ) := m12S3C0W.toList.drop 2

@[expose] def d1 : List (List ℤ) := m12S3C1W.toList.drop 2

meta def ab : Array (Array Nat) := #[m12S3A, m12S3B]

end CertificateChecks.KernelB3S3.M12

end

#ks_rawchain CertificateChecks.KernelB3S3.M12.C0 12 4 12
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m12S3C0S
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m12S3C0Base 2 CertificateChecks.KernelB3S3.M12.d0
#ks_rawchain CertificateChecks.KernelB3S3.M12.C1 12 4 12
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m12S3C1S
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m12S3C1Base 2 CertificateChecks.KernelB3S3.M12.d1
#kmisc_packarrs CertificateChecks.KernelB3S3.M12.AB CertificateChecks.KernelB3S3.M12.ab 4
#kmisc_packarrs CertificateChecks.KernelB3S3.M12.QG
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m12S3QGens 4
#kmisc_packarrs CertificateChecks.KernelB3S3.M12.LX
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m12S3Lines 4
#kmisc_packarrs CertificateChecks.KernelB3S3.M12.H
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m12S3Trans 4
#kmisc_packarrs CertificateChecks.KernelB3S3.M12.XC
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m12S3CaseX 4
#kb3_enum CertificateChecks.KernelB3S3.M12.EQ
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m12S3QGens
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m12S3C0Base 12 4
#kb3_enum CertificateChecks.KernelB3S3.M12.E0
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m12S3C0Gens
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m12S3C0Base 12 4
#kb3_enum CertificateChecks.KernelB3S3.M12.E1
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m12S3C1Gens
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m12S3C1Base 12 4

public section

namespace CertificateChecks.KernelB3S3.M12

open CFSG.HardMathSupport.Solomon.Coordinator.B3S3 CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ChainTail CFSG.KC.B3S3K

theorem szOK' : szOK 12 4 = true := by quickRfl

theorem bA : arrBind m12S3A 12 4 (AB 0) = true := by quickRfl

theorem bB : arrBind m12S3B 12 4 (AB 1) = true := by quickRfl

theorem pAB : permB 12 4 (AB 0) = true ∧ permB 12 4 (AB 1) = true := ⟨by quickRfl, by quickRfl⟩

theorem bS0 : ∀ j < 10, arrBind m12S3C0S[j]! 12 4 (C0.S j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem bS1 : ∀ j < 10, arrBind m12S3C1S[j]! 12 4 (C1.S j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem bQ : ∀ j < 2, arrBind m12S3QGens[j]! 12 4 (QG j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem bL : ∀ j < 13, arrBind m12S3Lines[j]! 12 4 (LX j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem bH : ∀ j < 13, arrBind m12S3Trans[j]! 12 4 (H j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem bX : ∀ j < 2, arrBind m12S3CaseX[j]! 12 4 (XC j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem bG0 : ∀ j < 4, arrBind m12S3C0Gens[j]! 12 4 (E0.G j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem bG1 : ∀ j < 4, arrBind m12S3C1Gens[j]! 12 4 (E1.G j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem bQE : ∀ j < 2, Nat.beq (EQ.G j) (QG j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem perm0 : allN 10 (fun j => permOK 12 4 (mask 4) (12 * 4) (C0.S j) (C0.SI j)) = true := by
  quickRfl

theorem perm1 : allN 10 (fun j => permOK 12 4 (mask 4) (12 * 4) (C1.S j) (C1.SI j)) = true := by
  quickRfl

theorem head0 : Nat.beq (C0.S 0) (AB 0) = true ∧ Nat.beq (C0.S 1) (AB 1) = true :=
  ⟨by quickRfl, by quickRfl⟩

theorem head1 : Nat.beq (C1.S 0) (AB 0) = true ∧ Nat.beq (C1.S 1) (AB 1) = true :=
  ⟨by quickRfl, by quickRfl⟩

theorem bget0 : ∀ t < 12, m12S3C0Base[t]! = pg 4 (mask 4) C0.BP t := by decide +kernel

theorem bget1 : ∀ t < 12, m12S3C1Base[t]! = pg 4 (mask 4) C1.BP t := by decide +kernel

theorem lines : linesK 12 4 3 EQ.N 13 EQ.T LX = true := by quickRfl

theorem trans : transK 12 4 13 H XC LX m12S3Rec = true := by quickRfl

theorem siftQ : ∀ k < 2, Nat.beq (Nat.shiftRight (QG k) (12 * 4)) 0 = true ∧
    allN 12 (fun t => Nat.blt (pg 4 (mask 4) (QG k) t) 12) = true ∧
    siftK 12 4 (mask 4) (12 * 4) (pidn 12 4) C0.LR C0.TRI C0.BP 12 0 (QG k) = true := by
  intro k hk
  interval_cases k <;> exact ⟨by quickRfl, by quickRfl, by quickRfl⟩

theorem siftH : ∀ k < 13, Nat.beq (Nat.shiftRight (H k) (12 * 4)) 0 = true ∧
    allN 12 (fun t => Nat.blt (pg 4 (mask 4) (H k) t) 12) = true ∧
    siftK 12 4 (mask 4) (12 * 4) (pidn 12 4) C0.LR C0.TRI C0.BP 12 0 (H k) = true := by
  intro k hk
  interval_cases k <;> exact ⟨by quickRfl, by quickRfl, by quickRfl⟩

theorem siftG0 : ∀ k < 4, Nat.beq (Nat.shiftRight (E0.G k) (12 * 4)) 0 = true ∧
    allN 12 (fun t => Nat.blt (pg 4 (mask 4) (E0.G k) t) 12) = true ∧
    siftK 12 4 (mask 4) (12 * 4) (pidn 12 4) C0.LR C0.TRI C0.BP 12 0 (E0.G k) = true := by
  intro k hk
  interval_cases k <;> exact ⟨by quickRfl, by quickRfl, by quickRfl⟩

theorem siftG1 : ∀ k < 4, Nat.beq (Nat.shiftRight (E1.G k) (12 * 4)) 0 = true ∧
    allN 12 (fun t => Nat.blt (pg 4 (mask 4) (E1.G k) t) 12) = true ∧
    siftK 12 4 (mask 4) (12 * 4) (pidn 12 4) C1.LR C1.TRI C1.BP 12 0 (E1.G k) = true := by
  intro k hk
  interval_cases k <;> exact ⟨by quickRfl, by quickRfl, by quickRfl⟩

theorem rels0 : relsK 12 4 3 C0.BP (XC 0) 12 m12S3C0Rels = true := by quickRfl

theorem rels1 : relsK 12 4 3 C1.BP (XC 1) 12 m12S3C1Rels = true := by quickRfl

theorem comm0 : commK 12 4 4 (XC 0) E0.G = true := by quickRfl

theorem comm1 : commK 12 4 4 (XC 1) E1.G = true := by quickRfl

theorem x0 : permB 12 4 (XC 0) = true ∧ Nat.beq (pw 12 4 (XC 0) 3) (pidn 12 4) = true :=
  ⟨by quickRfl, by quickRfl⟩

theorem x1 : permB 12 4 (XC 1) = true ∧ Nat.beq (pw 12 4 (XC 1) 3) (pidn 12 4) = true :=
  ⟨by quickRfl, by quickRfl⟩

theorem rc0 : Nat.beq (rcnt (C0.LR 0)) 12 = true := by quickRfl

theorem rc1 : Nat.beq (rcnt (C1.LR 0)) 12 = true := by quickRfl

theorem tail0 : allN 12 (ptailBranchK 12 4 C0.LR C0.TR C0.BP (XC 0) (pw 12 4 (XC 0))
    m12S3C0Rels E0.N E0.T 12) = true := by quickRfl

theorem tail1 : allN 12 (ptailBranchK 12 4 C1.LR C1.TR C1.BP (XC 1) (pw 12 4 (XC 1))
    m12S3C1Rels E1.N E1.T 12) = true := by quickRfl

theorem orb0 : Nat.beq (((List.range 12).map fun i => rcnt (C0.LR i)).prod) 95040 = true := by
  quickRfl

theorem pL : allN 13 (fun j => permB 12 4 (LX j)) = true := by quickRfl

theorem pQ : allN 2 (fun j => permB 12 4 (QG j)) = true := by quickRfl

theorem n0 : Nat.beq EQ.N 27 = true ∧ Nat.beq E0.N 54 = true ∧ Nat.beq E0.ng 4 = true ∧
    Nat.beq EQ.ng 2 = true ∧ Nat.beq E1.N 36 = true ∧ Nat.beq E1.ng 4 = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

end CertificateChecks.KernelB3S3.M12

end
