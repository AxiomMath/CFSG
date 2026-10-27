module

public import Certificates.Kernel.Co3Five.Data
public import Certificates.Kernel.Sporadic.Co3.C
public import Certificates.Data.Kernel.Misc.ChainTail
public import Certificates.Data.Kernel.Misc.PermWit
public import Certificates.Data.Kernel.Misc.ArrEnum
public import Certificates.Data.Kernel.BfsPinBase
public import Certificates.Data.Kernel.B3S3K
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.EachUnfold

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelCo3Five

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.PermWit CFSG.KC.Misc.ChainTail
open CFSG.KC.Misc.ArrEnum (permB memK)
open CFSG.KC.B3S3K (cm pw)
open CFSG.KC.LQT.P (anyN)

@[expose] noncomputable def I : ℕ := pidn 276 9

@[expose] noncomputable def cj (g y : ℕ) : ℕ := cm 276 9 g (cm 276 9 y (pinvS 276 9 (mask 9) g))

@[expose] noncomputable def cmt (g h : ℕ) : ℕ :=
  cm 276 9 (cm 276 9 g h) (cm 276 9 (pinvS 276 9 (mask 9) g) (pinvS 276 9 (mask 9) h))

@[expose] noncomputable def hP (j : ℕ) : ℕ :=
  if j = 0 ∨ j = 25 then I else if j < 25 then FC.F (j + 10) else FC.F (j + 9)

@[expose] noncomputable def lineP (j : ℕ) : ℕ :=
  if j = 0 then FC.F 0 else if j = 25 then FC.F 1 else cj (hP j) (FC.F 0)

@[expose] noncomputable def cmK (p q : ℕ) : Bool := Nat.beq (cm 276 9 p q) (cm 276 9 q p)

@[expose] noncomputable def sk25 : List ℕ := (List.range 1500).map K25
@[expose] noncomputable def skQ : List ℕ := (List.range 125).map KQ
@[expose] noncomputable def sk0 : List ℕ := (List.range 300).map K0
@[expose] noncomputable def skD : List ℕ := (List.range 60).map KD

@[expose] noncomputable def br (k : ℕ) : Bool :=
  ptailBranchK 276 9 CertificateChecks.KernelSpor.Co3C.LR CertificateChecks.KernelSpor.Co3C.TR
    CertificateChecks.KernelSpor.Co3C.BP (FC.F 1) (pw 276 9 (FC.F 1))
    CFSG.RankThree.Native.co3FiveRels S25.N S25.T 7 k

@[expose] noncomputable def fixZ (i : ℕ) : ℕ :=
  cntK 276 (fun q => Nat.beq (pg 9 (mask 9) (ZZ 0) q) q &&
    Nat.blt (rpos 9 (mask 9) (276 * 9) (CertificateChecks.KernelSpor.Co3C.LR i) q)
      (rcnt (CertificateChecks.KernelSpor.Co3C.LR i)))

@[expose] noncomputable def c25Pt (k : ℕ) : Bool :=
  !(cmK (S25.T k) (FC.F 2) && cmK (S25.T k) (FC.F 3)) ||
    anyN 5 fun e => Nat.beq (S25.T k) (pw 276 9 (FC.F 1) e)

@[expose] noncomputable def c0Pt (k : ℕ) : Bool :=
  !(cmK (S0.T k) (DG 0) && cmK (S0.T k) (DG 1)) ||
    anyN 5 fun e => Nat.beq (S0.T k) (pw 276 9 (FC.F 0) e)

theorem kW : szOK 276 9 = true := by quickRfl

theorem kPerm : allN 40 (fun k => permB 276 9 (FC.F k)) = true := by quickRfl

theorem kPerm2 : (permB 276 9 I && allN 31 (fun j => permB 276 9 (LN j)) && permB 276 9 (ZZ 0) &&
    permB 276 9 (DG 0) && permB 276 9 (DG 1)) = true := by quickRfl

theorem kSift : (allN 40 (fun k => siftR 276 9 CertificateChecks.KernelSpor.Co3C.LR
    CertificateChecks.KernelSpor.Co3C.TRI CertificateChecks.KernelSpor.Co3C.BP 7 (FC.F k)) &&
    siftR 276 9 CertificateChecks.KernelSpor.Co3C.LR CertificateChecks.KernelSpor.Co3C.TRI
      CertificateChecks.KernelSpor.Co3C.BP 7 I) = true := by quickRfl

theorem kLN : allN 31 (fun j => Nat.beq (LN j) (lineP j)) = true := by quickRfl

theorem kZD : (Nat.beq (ZZ 0) (cj (FC.F 10) (FC.F 0)) && Nat.beq (DG 0) (cmt (FC.F 6) (FC.F 7)) &&
    Nat.beq (DG 1) (FC.F 7)) = true := by quickRfl

theorem kNums : (Nat.beq S25.ng 4 && Nat.beq S25.N 1500 && Nat.beq SQ.ng 2 && Nat.beq SQ.N 125 &&
    Nat.beq S0.ng 3 && Nat.beq S0.N 300 && Nat.beq SD.ng 2 && Nat.beq SD.N 60) = true := by
  quickRfl

theorem kGens : (allN 4 (fun k => Nat.beq (S25.G k) (FC.F (k + 2))) &&
    allN 2 (fun k => Nat.beq (SQ.G k) (FC.F (k + 2))) &&
    Nat.beq (S0.G 0) (FC.F 0) && Nat.beq (S0.G 1) (FC.F 6) && Nat.beq (S0.G 2) (FC.F 7) &&
    Nat.beq (SD.G 0) (DG 0) && Nat.beq (SD.G 1) (DG 1)) = true := by quickRfl

theorem kK25 : keysSK 276 9 CFSG.RankThree.Native.co3FiveKeyPts S25.N S25.T sk25 = true := by
  quickRfl
theorem kKQ : keysSK 276 9 CFSG.RankThree.Native.co3FiveKeyPts SQ.N SQ.T skQ = true := by quickRfl
theorem kK0 : keysSK 276 9 CFSG.RankThree.Native.co3FiveKeyPts S0.N S0.T sk0 = true := by quickRfl
theorem kKD : keysSK 276 9 CFSG.RankThree.Native.co3FiveKeyPts SD.N SD.T skD = true := by quickRfl

theorem kTperm : (allN 1500 (fun i => permB 276 9 (S25.T i)) &&
    allN 125 (fun i => permB 276 9 (SQ.T i)) && allN 300 (fun i => permB 276 9 (S0.T i)) &&
    allN 60 (fun i => permB 276 9 (SD.T i))) = true := by quickRfl

theorem kZ : allN 4 (fun i => Nat.beq (pg 9 (mask 9) (ZZ 0) i) i) = true := by quickRfl

theorem kFix : (Nat.beq (fixZ 0) 6 && Nat.beq (fixZ 1) 5 && Nat.beq (fixZ 2) 2 &&
    Nat.beq (fixZ 3) 1) = true := by quickRfl

theorem kTail : ptailK 276 9 CertificateChecks.KernelSpor.Co3C.LR
    CertificateChecks.KernelSpor.Co3C.TR CertificateChecks.KernelSpor.Co3C.BP (ZZ 0)
    (pw 276 9 (ZZ 0)) [] 5 (pw 276 9 (ZZ 0)) 3 4 I = true := by quickRfl

theorem kRels : CFSG.KC.B3S3K.relsK 276 9 5 CertificateChecks.KernelSpor.Co3C.BP (FC.F 1) 7
    CFSG.RankThree.Native.co3FiveRels = true := by quickRfl

theorem kRc : Nat.beq (rcnt (CertificateChecks.KernelSpor.Co3C.LR 0)) 276 = true ∧
    Nat.beq (rcnt (CertificateChecks.KernelSpor.Co3C.LR 1)) 275 = true := ⟨by quickRfl, by quickRfl⟩

theorem kBr : allN 275 (fun k => br (k + 1)) = true := by quickRfl

@[expose] noncomputable def acc0 : ℕ :=
  CertificateChecks.KernelSpor.Co3C.TR
    (Nat.add (roff 276 (Nat.mul 276 9) (CertificateChecks.KernelSpor.Co3C.LR 0)) 0)

@[expose] noncomputable def sub1 (k : ℕ) : Bool :=
  !(relOKK 9 (mask 9) CertificateChecks.KernelSpor.Co3C.BP (pw 276 9 (FC.F 1))
      CFSG.RankThree.Native.co3FiveRels 1 acc0
      (rpt 9 (mask 9) (CertificateChecks.KernelSpor.Co3C.LR 1) k)) ||
    ptailK 276 9 CertificateChecks.KernelSpor.Co3C.LR CertificateChecks.KernelSpor.Co3C.TR
      CertificateChecks.KernelSpor.Co3C.BP (FC.F 1) (pw 276 9 (FC.F 1))
      CFSG.RankThree.Native.co3FiveRels S25.N S25.T 5 2
      (pcomp 276 9 (mask 9) acc0 (CertificateChecks.KernelSpor.Co3C.TR
        (Nat.add (roff 276 (Nat.mul 276 9) (CertificateChecks.KernelSpor.Co3C.LR 1)) k)))

@[expose] noncomputable def kSF (j : Nat) : Bool := allN 11 (fun k => sub1 (j * 11 + k))

#kc_each_unfold kSF 0 10 as CertificateChecks.KernelCo3Five.kS0
#kc_each_unfold kSF 10 25 as CertificateChecks.KernelCo3Five.kS

theorem kQ5 : allN 125 (fun k => Nat.beq (pw 276 9 (SQ.T k) 5) I) = true := by quickRfl

theorem kQW : allN 125 (fun k => Nat.beq (SQ.T k) I || (Nat.blt (WQ k / 5) 31 &&
    Nat.beq (SQ.T k) (pw 276 9 (LN (WQ k / 5)) (WQ k % 5)))) = true := by quickRfl

theorem kQD : allN 31 (fun j => allN 31 fun j' => j == j' ||
    allN 5 fun e => !Nat.beq (LN j) (pw 276 9 (LN j') e)) = true := by quickRfl

theorem kQL : allN 31 (fun j => Nat.beq (pw 276 9 (LN j) 5) I && !Nat.beq (LN j) I &&
    memK SQ.N SQ.T (LN j)) = true := by quickRfl

theorem kC25a : (allN 4 (fun k => cmK (FC.F (k + 2)) (FC.F 1)) && memK S25.N S25.T (FC.F 2) &&
    memK S25.N S25.T (FC.F 3) &&
    allN 4 (fun k => allN 2 fun l => memK SQ.N SQ.T (cj (FC.F (k + 2)) (FC.F (l + 2))))) = true := by
  quickRfl

theorem kC25b0 : allN 250 (fun k => c25Pt k) = true := by quickRfl
theorem kC25b1 : allN 250 (fun k => c25Pt (250 + k)) = true := by quickRfl
theorem kC25b2 : allN 250 (fun k => c25Pt (500 + k)) = true := by quickRfl
theorem kC25b3 : allN 250 (fun k => c25Pt (750 + k)) = true := by quickRfl
theorem kC25b4 : allN 250 (fun k => c25Pt (1000 + k)) = true := by quickRfl
theorem kC25b5 : allN 250 (fun k => c25Pt (1250 + k)) = true := by quickRfl

theorem kC0a : (cmK (FC.F 0) (FC.F 0) && cmK (FC.F 6) (FC.F 0) && cmK (FC.F 7) (FC.F 0) &&
    memK S0.N S0.T (FC.F 8) && memK S0.N S0.T (FC.F 9) &&
    Nat.beq (FC.F 7) (cmt (FC.F 8) (FC.F 9)) &&
    allN 3 (fun k => allN 2 fun l => memK SD.N SD.T (cj (S0.G k) (DG l))) &&
    allN 3 (fun k => allN 3 fun l => memK SD.N SD.T (cmt (S0.G k) (S0.G l))) &&
    !cmK (DG 0) (DG 1)) = true := by quickRfl

theorem kC0b : allN 300 (fun k => c0Pt k) = true := by quickRfl

theorem kTree : allN 60 (fun k => Nat.beq (SD.T k) I ||
    allN 60 (ctreePt 276 9 60 k SD.T (WT k))) = true := by quickRfl

theorem kD0 : Nat.beq (SD.T 0) I = true := by quickRfl

end CertificateChecks.KernelCo3Five

end
