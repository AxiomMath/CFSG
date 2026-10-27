module

public import Certificates.Data.I19Spor3
public import Certificates.Data.Kernel.B3S3K
public import Certificates.Data.Kernel.Misc.ChainTail
public import Certificates.Kernel.B3S3.Gen
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.SporSch.Th.GenV4
public meta import Certificates.Data.I19Spor3
public meta import Certificates.Kernel.B3S3.Gen
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelB3S3.M11

open CFSG.HardMathSupport.Solomon.Coordinator.B3S3

@[expose] def d0 : List (List ℤ) := m11S3C0W.toList.drop 2

meta def ab : Array (Array Nat) := #[m11S3A, m11S3B]

meta def pts0 : Array (Array Nat) := (CFSG.KC.BfsGen.search 11 4 m11S3C0Gens).1

meta def wj : List Nat := (CFSG.KC.B3S3Gen.convWit 11 pts0 [2] [1]).1

meta def wr : List Nat := (CFSG.KC.B3S3Gen.convWit 11 pts0 [2] [1]).2

end CertificateChecks.KernelB3S3.M11

end

#ks_rawchain CertificateChecks.KernelB3S3.M11.C0 11 4 11
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m11S3C0S
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m11S3C0Base 2 CertificateChecks.KernelB3S3.M11.d0
#kmisc_packarrs CertificateChecks.KernelB3S3.M11.AB CertificateChecks.KernelB3S3.M11.ab 4
#kmisc_packarrs CertificateChecks.KernelB3S3.M11.QG
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m11S3QGens 4
#kmisc_packarrs CertificateChecks.KernelB3S3.M11.LX
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m11S3Lines 4
#kmisc_packarrs CertificateChecks.KernelB3S3.M11.H
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m11S3Trans 4
#kmisc_packarrs CertificateChecks.KernelB3S3.M11.XC
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m11S3CaseX 4
#kb3_enum CertificateChecks.KernelB3S3.M11.EQ
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m11S3QGens
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m11S3C0Base 11 4
#kb3_enum CertificateChecks.KernelB3S3.M11.E0
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m11S3C0Gens
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m11S3C0Base 11 4
#kss_natlist CertificateChecks.KernelB3S3.M11.WJ CertificateChecks.KernelB3S3.M11.wj
#kss_natlist CertificateChecks.KernelB3S3.M11.WR CertificateChecks.KernelB3S3.M11.wr

public section

namespace CertificateChecks.KernelB3S3.M11

open CFSG.HardMathSupport.Solomon.Coordinator.B3S3 CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ChainTail CFSG.KC.B3S3K

theorem szOK' : szOK 11 4 = true := by quickRfl

theorem bA : arrBind m11S3A 11 4 (AB 0) = true := by quickRfl

theorem bB : arrBind m11S3B 11 4 (AB 1) = true := by quickRfl

theorem pAB : permB 11 4 (AB 0) = true ∧ permB 11 4 (AB 1) = true := ⟨by quickRfl, by quickRfl⟩

theorem bS : ∀ j < 6, arrBind m11S3C0S[j]! 11 4 (C0.S j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem bQ : ∀ j < 2, arrBind m11S3QGens[j]! 11 4 (QG j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem bL : ∀ j < 4, arrBind m11S3Lines[j]! 11 4 (LX j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem bH : ∀ j < 4, arrBind m11S3Trans[j]! 11 4 (H j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem bX : arrBind m11S3CaseX[0]! 11 4 (XC 0) = true := by quickRfl

theorem bG : ∀ j < 3, arrBind m11S3C0Gens[j]! 11 4 (E0.G j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem bQE : ∀ j < 2, Nat.beq (EQ.G j) (QG j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem perm0 : allN 6 (fun j => permOK 11 4 (mask 4) (11 * 4) (C0.S j) (C0.SI j)) = true := by
  quickRfl

theorem head0 : Nat.beq (C0.S 0) (AB 0) = true ∧ Nat.beq (C0.S 1) (AB 1) = true :=
  ⟨by quickRfl, by quickRfl⟩

theorem bget0 : ∀ t < 11, m11S3C0Base[t]! = pg 4 (mask 4) C0.BP t := by decide +kernel

theorem lines : linesK 11 4 3 EQ.N 4 EQ.T LX = true := by quickRfl

theorem trans : transK 11 4 4 H XC LX m11S3Rec = true := by quickRfl

theorem siftQ : ∀ k < 2, Nat.beq (Nat.shiftRight (QG k) (11 * 4)) 0 = true ∧
    allN 11 (fun t => Nat.blt (pg 4 (mask 4) (QG k) t) 11) = true ∧
    siftK 11 4 (mask 4) (11 * 4) (pidn 11 4) C0.LR C0.TRI C0.BP 11 0 (QG k) = true := by
  intro k hk
  interval_cases k <;> exact ⟨by quickRfl, by quickRfl, by quickRfl⟩

theorem siftH : ∀ k < 4, Nat.beq (Nat.shiftRight (H k) (11 * 4)) 0 = true ∧
    allN 11 (fun t => Nat.blt (pg 4 (mask 4) (H k) t) 11) = true ∧
    siftK 11 4 (mask 4) (11 * 4) (pidn 11 4) C0.LR C0.TRI C0.BP 11 0 (H k) = true := by
  intro k hk
  interval_cases k <;> exact ⟨by quickRfl, by quickRfl, by quickRfl⟩

theorem siftG : ∀ k < 3, Nat.beq (Nat.shiftRight (E0.G k) (11 * 4)) 0 = true ∧
    allN 11 (fun t => Nat.blt (pg 4 (mask 4) (E0.G k) t) 11) = true ∧
    siftK 11 4 (mask 4) (11 * 4) (pidn 11 4) C0.LR C0.TRI C0.BP 11 0 (E0.G k) = true := by
  intro k hk
  interval_cases k <;> exact ⟨by quickRfl, by quickRfl, by quickRfl⟩

theorem rels0 : relsK 11 4 3 C0.BP (XC 0) 11 m11S3C0Rels = true := by quickRfl

theorem comm0 : commK 11 4 3 (XC 0) E0.G = true := by quickRfl

theorem x0 : permB 11 4 (XC 0) = true ∧ Nat.beq (pw 11 4 (XC 0) 3) (pidn 11 4) = true :=
  ⟨by quickRfl, by quickRfl⟩

theorem rc0 : Nat.beq (rcnt (C0.LR 0)) 11 = true := by quickRfl

theorem tail0 : allN 11 (ptailBranchK 11 4 C0.LR C0.TR C0.BP (XC 0) (pw 11 4 (XC 0))
    m11S3C0Rels E0.N E0.T 11) = true := by quickRfl

theorem conv0 : allN E0.N (convAt 11 4 E0.N E0.T [2] [1] WJ WR) = true := by quickRfl

theorem orb0 : Nat.beq (((List.range 11).map fun i => rcnt (C0.LR i)).prod) 7920 = true := by
  quickRfl

theorem pL : allN 4 (fun j => permB 11 4 (LX j)) = true := by quickRfl

theorem pQ : allN 2 (fun j => permB 11 4 (QG j)) = true := by quickRfl

theorem n0 : Nat.beq EQ.N 9 = true ∧ Nat.beq E0.N 18 = true ∧ Nat.beq E0.ng 3 = true ∧
    Nat.beq EQ.ng 2 = true := ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

end CertificateChecks.KernelB3S3.M11

end
