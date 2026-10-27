module

public import Certificates.Kernel.Co3K.Text
public import Certificates.Kernel.Sporadic.Co3.T
public import Certificates.Kernel.Sporadic.Co3.C
public import Certificates.Kernel.Sporadic.Co3.M
public import Certificates.Kernel.Sporadic.Co3.Single
public import Certificates.Data.Kernel.Co3K
public import Certificates.Data.Kernel.Misc.ArrEnum
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo3K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Co3K CFSG.KC.Misc.ArrEnum
open CertificateChecks.KernelSpor

theorem perms : allN 28 (fun j => bAnd(permB 276 9 (KT.L j),
    canonK 276 9 (mask 9) (276 * 9) (KT.L j))) = true := by quickRfl

theorem hiR : allN 5 (fun j => bAnd(Nat.beq (Nat.shiftRight (KT.L j) (276 * 9)) 0,
    allN 276 (fun i => Nat.blt (pg 9 (mask 9) (KT.L j) i) 276))) = true := by quickRfl

theorem sE : Co3T.sift (KT.L 0) = true := by quickRfl
theorem sT1 : Co3T.sift (KT.L 1) = true := by quickRfl
theorem sG1 : Co3C.sift (KT.L 2) = true := by quickRfl
theorem sX5 : Co3M.sift (KT.L 3) = true := by quickRfl
theorem sX7 : Co3M.sift (KT.L 4) = true := by quickRfl

theorem kId : idK 276 9 (mask 9) = true := by quickRfl
theorem cId : canonK 276 9 (mask 9) (276 * 9) idk = true := by quickRfl
theorem cZ : canonK 276 9 (mask 9) (276 * 9) Co3Z = true := by quickRfl

theorem eSq : Nat.beq (pk (KT.L 0) (KT.L 0)) idk = true := by quickRfl
theorem eNe : bIf(Nat.beq (KT.L 0) idk, false, true) = true := by quickRfl
theorem eNz : bIf(Nat.beq (KT.L 0) Co3Z, false, true) = true := by quickRfl
theorem t1E : Nat.beq (pk (KT.L 1) (KT.L 0)) (pk (pk (KT.L 0) Co3Z) (KT.L 1)) = true := by quickRfl
theorem g1E : Nat.beq (pk (KT.L 2) (KT.L 0)) (pk Co3Z (KT.L 2)) = true := by quickRfl
theorem x5P : Nat.beq (powK (KT.L 3) 5) idk = true := by quickRfl
theorem x5Ne : bIf(Nat.beq (KT.L 3) idk, false, true) = true := by quickRfl
theorem x7P : Nat.beq (powK (KT.L 4) 7) idk = true := by quickRfl
theorem x7Ne : bIf(Nat.beq (KT.L 4) idk, false, true) = true := by quickRfl

theorem gens : allN 8 (fun k => bAnd(canonK 276 9 (mask 9) (276 * 9) (Co3T.S k),
    canonK 276 9 (mask 9) (276 * 9) (Co3T.SI k))) = true := by quickRfl

theorem cnt0 : Nat.beq (rcnt (Co3T.LR 0)) 128 = true := by quickRfl

theorem trs : allN 3 (fun i => allN (rcnt (Co3T.LR i)) (fun k =>
    canonK 276 9 (mask 9) (276 * 9) (Co3T.TR (Nat.add (roff 276 (276 * 9) (Co3T.LR i)) k)))) =
    true := by quickRfl

@[expose] noncomputable def eS (a0 : Nat) : Bool :=
  strictB (KT.L 0) (fun E => strictB (pk E Co3Z) (fun EZ =>
    allN 16 (fun a => prod3K Co3T.LR Co3T.TR (eK E EZ) (Nat.add a0 a))))

@[expose] noncomputable def kS (a0 : Nat) : Bool :=
  allN 16 (fun a => prod3K Co3T.LR Co3T.TR (k3K Co3T.S Co3T.SI (fun i => KT.L (Nat.add 5 i)))
    (Nat.add a0 a))

theorem eS0 : eS 0 = true := by quickRfl
theorem eS1 : eS 16 = true := by quickRfl
theorem eS2 : eS 32 = true := by quickRfl
theorem eS3 : eS 48 = true := by quickRfl
theorem eS4 : eS 64 = true := by quickRfl
theorem eS5 : eS 80 = true := by quickRfl
theorem eS6 : eS 96 = true := by quickRfl
theorem eS7 : eS 112 = true := by quickRfl

theorem kS0 : kS 0 = true := by quickRfl
theorem kS1 : kS 16 = true := by quickRfl
theorem kS2 : kS 32 = true := by quickRfl
theorem kS3 : kS 48 = true := by quickRfl
theorem kS4 : kS 64 = true := by quickRfl
theorem kS5 : kS 80 = true := by quickRfl
theorem kS6 : kS 96 = true := by quickRfl
theorem kS7 : kS 112 = true := by quickRfl

@[expose] noncomputable def WT : Nat := packL 72 (wK Co3T.S Co3T.SI)

theorem wt : strictB WT (fun T => allN 72 (fun k => bAnd(Nat.beq (lane T k) (wK Co3T.S Co3T.SI k),
    canonK 276 9 (mask 9) (276 * 9) (lane T k)))) = true := by quickRfl

@[expose] noncomputable def k5 (i0 n : Nat) : Bool :=
  strictB WT (fun T => allN n (fun i =>
    k5RowK (fun i => KT.L (Nat.add 5 i)) T Co3Z (Nat.add i0 i)))

theorem k5a : k5 0 12 = true := by quickRfl
theorem k5b : k5 12 11 = true := by quickRfl

end CertificateChecks.KernelCo3K

end
