module

public import Certificates.Data.B3Spor3.M24
public import Certificates.Data.Kernel.B3S3K
public import Certificates.Data.Kernel.Misc.ChainTail
public import Certificates.Data.Kernel.Misc.ChainTailLv
public import Certificates.Kernel.B3S3.Gen
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.SporSch.Th.GenV4
public meta import Certificates.Data.B3Spor3.M24
public meta import Certificates.Kernel.B3S3.Gen
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import CFSG.RankThree.Native.PermEnumeration
public meta import CFSG.RankThree.Native.ChainCentralizer
public meta import CFSG.RankThree.PartOne.KS.PKit
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

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.RankThree.Native
  CFSG.RankThree.PartOne in
meta def orbT (S : Array (Array Nat)) (base : Array Nat) (gs : Array (Array Nat)) (N : Nat)
    (x : Array Nat) (rels : List (Nat × Nat × Nat)) : List Nat × List Nat × List Nat := Id.run do
  let p := ((rawLevels 24 S base)[0]!).pts
  let c := (enumBfs 24 gs base.toList (N + 1)).pts
  let xs := powPA 3 24 x
  let mut idx := Array.replicate 24 0
  for k in [0:p.size] do
    idx := idx.set! (p[k]!) k
  let mut ri := Array.replicate p.size p.size
  let mut ek := Array.replicate p.size 0
  let mut reps : Array Nat := #[]
  for k in [0:p.size] do
    if ri[k]! == p.size && relOK base xs rels 0 (idA 24) p[k]! then
      let j := reps.size
      reps := reps.push k
      let q := p[k]!
      for e in [0:c.size] do
        let t := idx.getD ((c.getD e #[]).getD q 0) 0
        if ri[t]! == p.size then
          ri := ri.set! t j
          ek := ek.set! t e
  return (reps.toList, (ri.map fun i => if i == p.size then 0 else i).toList, ek.toList)

meta def ob0 : List Nat × List Nat × List Nat :=
  orbT m24S3C0S m24S3C0Base m24S3C0Gens 1080 m24S3CaseX[0]! m24S3C0Rels

meta def ob1 : List Nat × List Nat × List Nat :=
  orbT m24S3C1S m24S3C1Base m24S3C1Gens 504 m24S3CaseX[1]! m24S3C1Rels

meta def rb0 : List Nat := ob0.1

meta def ri0 : List Nat := ob0.2.1

meta def ek0 : List Nat := ob0.2.2

meta def rb1 : List Nat := ob1.1

meta def ri1 : List Nat := ob1.2.1

meta def ek1 : List Nat := ob1.2.2

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
#kss_natlist CertificateChecks.KernelB3S3.M24.RB0 CertificateChecks.KernelB3S3.M24.rb0
#kss_natlist CertificateChecks.KernelB3S3.M24.RI0 CertificateChecks.KernelB3S3.M24.ri0
#kss_natlist CertificateChecks.KernelB3S3.M24.EK0 CertificateChecks.KernelB3S3.M24.ek0
#kss_natlist CertificateChecks.KernelB3S3.M24.RB1 CertificateChecks.KernelB3S3.M24.rb1
#kss_natlist CertificateChecks.KernelB3S3.M24.RI1 CertificateChecks.KernelB3S3.M24.ri1
#kss_natlist CertificateChecks.KernelB3S3.M24.EK1 CertificateChecks.KernelB3S3.M24.ek1

public section

namespace CertificateChecks.KernelB3S3.M24

open CFSG.HardMathSupport.Solomon.Coordinator.B3S3 CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ChainTail CFSG.KC.B3S3K

@[expose] def RLT0 : List (List (Nat × Nat × Nat)) :=
  [[(0, 0, 0), (0, 0, 1), (0, 0, 2)],
    [(1, 1, 0), (1, 1, 1), (1, 1, 2)],
    [(2, 2, 0), (2, 2, 1), (2, 2, 2)],
    [(3, 3, 0), (3, 3, 1), (3, 3, 2)],
    [(4, 4, 0), (4, 4, 1), (4, 4, 2)],
    [(5, 5, 0), (5, 5, 1), (5, 5, 2)],
    [(6, 6, 0)],
    [(6, 7, 1), (7, 7, 0), (7, 6, 2)],
    [(6, 8, 2), (7, 8, 1), (8, 8, 0), (8, 6, 1), (8, 7, 2)],
    [(9, 9, 0)],
    [(9, 10, 1), (10, 10, 0), (10, 9, 2)],
    [(9, 11, 2), (10, 11, 1), (11, 11, 0), (11, 9, 1), (11, 10, 2)],
    [(12, 12, 0)],
    [(12, 13, 1), (13, 13, 0), (13, 12, 2)],
    [(12, 14, 2), (13, 14, 1), (14, 14, 0), (14, 12, 1), (14, 13, 2)],
    [(15, 15, 0)],
    [(15, 16, 1), (16, 16, 0), (16, 15, 2)],
    [(15, 17, 2), (16, 17, 1), (17, 17, 0), (17, 15, 1), (17, 16, 2)],
    [(18, 18, 0)],
    [(18, 19, 1), (19, 19, 0), (19, 18, 2)],
    [(18, 20, 2), (19, 20, 1), (20, 20, 0), (20, 18, 1), (20, 19, 2)],
    [(21, 21, 0)],
    [(21, 22, 1), (22, 22, 0), (22, 21, 2)],
    [(21, 23, 2), (22, 23, 1), (23, 23, 0), (23, 21, 1), (23, 22, 2)]]

@[expose] def RLT1 : List (List (Nat × Nat × Nat)) :=
  [[(0, 0, 0)],
    [(0, 1, 1), (1, 1, 0), (1, 0, 2)],
    [(0, 2, 2), (1, 2, 1), (2, 2, 0), (2, 0, 1), (2, 1, 2)],
    [(3, 3, 0)],
    [(3, 4, 1), (4, 4, 0), (4, 3, 2)],
    [(3, 5, 2), (4, 5, 1), (5, 5, 0), (5, 3, 1), (5, 4, 2)],
    [(6, 6, 0)],
    [(6, 7, 1), (7, 7, 0), (7, 6, 2)],
    [(6, 8, 2), (7, 8, 1), (8, 8, 0), (8, 6, 1), (8, 7, 2)],
    [(9, 9, 0)],
    [(9, 10, 1), (10, 10, 0), (10, 9, 2)],
    [(9, 11, 2), (10, 11, 1), (11, 11, 0), (11, 9, 1), (11, 10, 2)],
    [(12, 12, 0)],
    [(12, 13, 1), (13, 13, 0), (13, 12, 2)],
    [(12, 14, 2), (13, 14, 1), (14, 14, 0), (14, 12, 1), (14, 13, 2)],
    [(15, 15, 0)],
    [(15, 16, 1), (16, 16, 0), (16, 15, 2)],
    [(15, 17, 2), (16, 17, 1), (17, 17, 0), (17, 15, 1), (17, 16, 2)],
    [(18, 18, 0)],
    [(18, 19, 1), (19, 19, 0), (19, 18, 2)],
    [(18, 20, 2), (19, 20, 1), (20, 20, 0), (20, 18, 1), (20, 19, 2)],
    [(21, 21, 0)],
    [(21, 22, 1), (22, 22, 0), (22, 21, 2)],
    [(21, 23, 2), (22, 23, 1), (23, 23, 0), (23, 21, 1), (23, 22, 2)]]

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

theorem rep0 : repBranchLK 24 5 C0.LR C0.TR C0.BP (XC 0) (pw 24 5 (XC 0)) (fun i => RLT0.getD i [])
    E0.N E0.T 24 (RB0 0) = true := by quickRfl

theorem kOrb0 : allN 24 (orbRelK 24 5 C0.LR C0.BP (pw 24 5 (XC 0)) m24S3C0Rels E0.N E0.T 1 RB0
    RI0 EK0) = true := by quickRfl

theorem rep1 : repBranchLK 24 5 C1.LR C1.TR C1.BP (XC 1) (pw 24 5 (XC 1)) (fun i => RLT1.getD i [])
    E1.N E1.T 24 (RB1 0) = true := by quickRfl

theorem kOrb1 : allN 24 (orbRelK 24 5 C1.LR C1.BP (pw 24 5 (XC 1)) m24S3C1Rels E1.N E1.T 1 RB1
    RI1 EK1) = true := by quickRfl

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
