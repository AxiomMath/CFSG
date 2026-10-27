module

public import Certificates.Data.Kernel.Co3Tw.Pairs
public import Certificates.Kernel.Co3Tw.Enum
public import Certificates.Kernel.Co3Tw.SrchData
public import Certificates.Kernel.Co3Tw.PairsData
public import Certificates.Kernel.Sporadic.Co3.C
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo3Tw

open CFSG.KC.Enum CFSG.KS CFSG.KC.Co3Tw CertificateChecks.KernelSpor

@[expose] noncomputable def dpK (k : Nat) : Nat :=
  nIf(Nat.beq k 0, SD.dp0, nIf(Nat.beq k 1, SD.dp1, nIf(Nat.beq k 2, SD.dp2, nIf(Nat.beq k 3, SD.dp3,
    nIf(Nat.beq k 4, SD.dp4, nIf(Nat.beq k 5, SD.dp5, SD.dp6))))))

@[expose] noncomputable def nthL (L : List (List Nat)) : Nat → List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun a _ ih r => Nat.rec (motive := fun _ => List Nat) a (fun r' _ => ih r') r) L

@[expose] noncomputable def prR (r : Nat) : Bool :=
  strictB (EP.T (f12 PD.rp r)) fun x =>
    bAnd(prChk 276 9 (mask 9) Co3C.BP 7 2187 173 PD.cc dpK EP.T x (nthL PD.pr r) 0,
      Nat.beq (Nat.mul (lenK (nthL PD.pr r)) (f12 PD.cn r)) (nat_lit 2187))

theorem ch431008cr : bAnd(crChk 9 (mask 9) Co3C.BP 7 2187 58 PD.rp EP.T PD.cr 0,
    Nat.beq (lenK PD.cr) 890) = true := by quickRfl

theorem ch431008cn : allN 58 (fun r => Nat.beq (cntR r PD.cr) (f12 PD.cn r)) = true := by quickRfl

theorem ch431008o3 : allN 58 (fun r => strictB (EP.T (f12 PD.rp r)) fun x =>
    bAnd(cubeB 9 (mask 9) Co3C.BP 7 x, !(idB 9 (mask 9) Co3C.BP 7 x))) = true := by quickRfl

#kc_each CertificateChecks.KernelCo3Tw ch431008pr_ prR 0 58

theorem neg431008pr : (!prChk 276 9 (mask 9) Co3C.BP 7 2187 173 PD.cc dpK EP.T (EP.T (f12 PD.rp 1))
    (nthL PD.pr 0) 0) = true := by quickRfl

theorem neg431008cn : (!allN 58 (fun r => Nat.beq (cntR r PD.cr) (f12 PD.cn (Nat.succ r) ))) = true := by
  quickRfl

end CertificateChecks.KernelCo3Tw

end
