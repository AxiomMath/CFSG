module

public import Certificates.Data.B3Spor3.M22
public import Certificates.Data.Kernel.B3S3K
public import Certificates.Data.Kernel.Misc.ChainTail
public import Certificates.Kernel.B3S3.Gen
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.SporSch.Th.GenV4
public meta import Certificates.Data.B3Spor3.M22
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelB3S3.M22

open CFSG.HardMathSupport.Solomon.Coordinator.B3S3

@[expose] def d0 : List (List ℤ) := m22S3C0W.toList.drop 2

meta def ab : Array (Array Nat) := #[m22S3A, m22S3B]

end CertificateChecks.KernelB3S3.M22

end

#ks_rawchain CertificateChecks.KernelB3S3.M22.C0 22 5 22
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m22S3C0S
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m22S3C0Base 2 CertificateChecks.KernelB3S3.M22.d0
#kmisc_packarrs CertificateChecks.KernelB3S3.M22.AB CertificateChecks.KernelB3S3.M22.ab 5
#kmisc_packarrs CertificateChecks.KernelB3S3.M22.QG
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m22S3QGens 5
#kmisc_packarrs CertificateChecks.KernelB3S3.M22.LX
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m22S3Lines 5
#kmisc_packarrs CertificateChecks.KernelB3S3.M22.H
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m22S3Trans 5
#kmisc_packarrs CertificateChecks.KernelB3S3.M22.XC
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m22S3CaseX 5
#kb3_enum CertificateChecks.KernelB3S3.M22.EQ
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m22S3QGens
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m22S3C0Base 22 5
#kb3_enum CertificateChecks.KernelB3S3.M22.E0
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m22S3C0Gens
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m22S3C0Base 22 5

public section

namespace CertificateChecks.KernelB3S3.M22

open CFSG.HardMathSupport.Solomon.Coordinator.B3S3 CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ChainTail CFSG.KC.B3S3K

theorem szOK' : szOK 22 5 = true := by quickRfl

theorem bA : arrBind m22S3A 22 5 (AB 0) = true := by quickRfl

theorem bB : arrBind m22S3B 22 5 (AB 1) = true := by quickRfl

theorem pAB : permB 22 5 (AB 0) = true ∧ permB 22 5 (AB 1) = true := ⟨by quickRfl, by quickRfl⟩

theorem bS : ∀ j < 11, arrBind m22S3C0S[j]! 22 5 (C0.S j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem bQ : ∀ j < 2, arrBind m22S3QGens[j]! 22 5 (QG j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem bL : ∀ j < 4, arrBind m22S3Lines[j]! 22 5 (LX j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem bH : ∀ j < 4, arrBind m22S3Trans[j]! 22 5 (H j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem bX : arrBind m22S3CaseX[0]! 22 5 (XC 0) = true := by quickRfl

theorem bG : ∀ j < 3, arrBind m22S3C0Gens[j]! 22 5 (E0.G j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem bQE : ∀ j < 2, Nat.beq (EQ.G j) (QG j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem perm0 : allN 11 (fun j => permOK 22 5 (mask 5) (22 * 5) (C0.S j) (C0.SI j)) = true := by
  quickRfl

theorem head0 : Nat.beq (C0.S 0) (AB 0) = true ∧ Nat.beq (C0.S 1) (AB 1) = true :=
  ⟨by quickRfl, by quickRfl⟩

theorem bget0 : ∀ t < 22, m22S3C0Base[t]! = pg 5 (mask 5) C0.BP t := by decide +kernel

theorem lines : linesK 22 5 3 EQ.N 4 EQ.T LX = true := by quickRfl

theorem trans : transK 22 5 4 H XC LX m22S3Rec = true := by quickRfl

theorem siftQ : ∀ k < 2, Nat.beq (Nat.shiftRight (QG k) (22 * 5)) 0 = true ∧
    allN 22 (fun t => Nat.blt (pg 5 (mask 5) (QG k) t) 22) = true ∧
    siftK 22 5 (mask 5) (22 * 5) (pidn 22 5) C0.LR C0.TRI C0.BP 22 0 (QG k) = true := by
  intro k hk
  interval_cases k <;> exact ⟨by quickRfl, by quickRfl, by quickRfl⟩

theorem siftH : ∀ k < 4, Nat.beq (Nat.shiftRight (H k) (22 * 5)) 0 = true ∧
    allN 22 (fun t => Nat.blt (pg 5 (mask 5) (H k) t) 22) = true ∧
    siftK 22 5 (mask 5) (22 * 5) (pidn 22 5) C0.LR C0.TRI C0.BP 22 0 (H k) = true := by
  intro k hk
  interval_cases k <;> exact ⟨by quickRfl, by quickRfl, by quickRfl⟩

theorem siftG : ∀ k < 3, Nat.beq (Nat.shiftRight (E0.G k) (22 * 5)) 0 = true ∧
    allN 22 (fun t => Nat.blt (pg 5 (mask 5) (E0.G k) t) 22) = true ∧
    siftK 22 5 (mask 5) (22 * 5) (pidn 22 5) C0.LR C0.TRI C0.BP 22 0 (E0.G k) = true := by
  intro k hk
  interval_cases k <;> exact ⟨by quickRfl, by quickRfl, by quickRfl⟩

theorem rels0 : relsK 22 5 3 C0.BP (XC 0) 22 m22S3C0Rels = true := by quickRfl

theorem comm0 : commK 22 5 3 (XC 0) E0.G = true := by quickRfl

theorem x0 : permB 22 5 (XC 0) = true ∧ Nat.beq (pw 22 5 (XC 0) 3) (pidn 22 5) = true :=
  ⟨by quickRfl, by quickRfl⟩

theorem rc0 : Nat.beq (rcnt (C0.LR 0)) 22 = true := by quickRfl

theorem tail0 : allN 22 (ptailBranchK 22 5 C0.LR C0.TR C0.BP (XC 0) (pw 22 5 (XC 0))
    m22S3C0Rels E0.N E0.T 22) = true := by quickRfl

theorem orb0 : Nat.beq (((List.range 22).map fun i => rcnt (C0.LR i)).prod) 443520 = true := by
  quickRfl

theorem pL : allN 4 (fun j => permB 22 5 (LX j)) = true := by quickRfl

theorem pQ : allN 2 (fun j => permB 22 5 (QG j)) = true := by quickRfl

theorem n0 : Nat.beq EQ.N 9 = true ∧ Nat.beq E0.N 36 = true ∧ Nat.beq E0.ng 3 = true ∧
    Nat.beq EQ.ng 2 = true := ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

end CertificateChecks.KernelB3S3.M22

end
