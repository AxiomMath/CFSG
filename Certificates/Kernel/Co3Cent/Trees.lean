module

public import Certificates.Kernel.Co3Cent.Data
public import Certificates.Kernel.Co3T.Data
public import Certificates.Kernel.Sporadic.Co3.C
public import Certificates.Data.Kernel.OrbRow.Defs
public import Certificates.Data.Kernel.Misc.PermWit
public import Certificates.Data.Kernel.Misc.ArrEnum
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CFSG.KD.Co3Cent

open CFSG.KC.Enum CFSG.KC.OrbRow CFSG.KC.PermWit
open CFSG.KC.Misc.ArrEnum (permB)

@[expose] noncomputable def maskDec3K (M : List Nat) (nl : Nat) : Bool :=
  allN (Nat.sub nl 1) (fun i => strictB (getS M (Nat.succ i)) fun a =>
    Nat.beq (Nat.land a (getS M i)) a)

@[expose] noncomputable def inP3K (S : List Nat) (j : Nat) : Bool :=
  strictB (getS S j) fun g => bAnd(permB 276 9 g,
    siftR 276 9 CertificateChecks.KernelSpor.Co3C.LR CertificateChecks.KernelSpor.Co3C.TRI
      CertificateChecks.KernelSpor.Co3C.BP 7 g)

theorem ch17370_tA : allN 11 (levelK 276 9 511 SA 17 BA KA MA DA RA) = true := by quickRfl

theorem ch17370_tB : allN 17 (levelK 276 9 511 SB 14 BB KB MB DB RB) = true := by quickRfl

theorem ch17370_tHA : allN 11 (levelK 276 9 511 SHA 17 BHA KHA MHA DHA RHA) = true := by quickRfl

theorem ch17370_tHB : allN 17 (levelK 276 9 511 SHB 12 BHB KHB MHB DHB RHB) = true := by quickRfl

theorem ch17370_f : bAnd(allN 11 (fun i => fixLvK 9 511 SA 17 (getS MA i) BA i),
    bAnd(allN 17 (fun i => fixLvK 9 511 SB 14 (getS MB i) BB i),
    bAnd(allN 11 (fun i => fixLvK 9 511 SHA 17 (getS MHA i) BHA i),
    bAnd(allN 17 (fun i => fixLvK 9 511 SHB 12 (getS MHB i) BHB i),
    bAnd(maskDec3K MA 11, bAnd(maskDec3K MB 17,
      bAnd(maskDec3K MHA 11, maskDec3K MHB 17))))))) = true := by
  quickRfl

theorem ch17370_k : bAnd(Nat.beq (lenS SA) 17, bAnd(Nat.beq (lenS BA) 11,
    bAnd(Nat.beq (lenS KA) 11, bAnd(Nat.beq (prodL KA) 495766656000,
    bAnd(Nat.beq (lenS SB) 14, bAnd(Nat.beq (lenS BB) 17, bAnd(Nat.beq (lenS KB) 17,
    bAnd(Nat.beq (prodL KB) 495766656000, bAnd(Nat.beq (lenS SHA) 17, bAnd(BHA == BA,
    bAnd(Nat.beq (lenS KHA) 11, bAnd(Nat.beq (prodL KHA) 349920, bAnd(Nat.beq (lenS SHB) 12,
    bAnd(BHB == BB, bAnd(Nat.beq (lenS KHB) 17, Nat.beq (prodL KHB) 29160))))))))))))))) =
      true := by
  quickRfl

theorem ch17370_s : bAnd(allN 17 (inP3K SA), bAnd(allN 14 (inP3K SB),
    bAnd(allN 17 (inP3K SHA), allN 12 (inP3K SHB)))) = true := by
  quickRfl

theorem ch17370_c :
    bAnd(allN 17 (fun j => commOK 276 9 511 (getS SHA j) (CertificateChecks.KernelCo3T.DE 9)),
    allN 12 (fun j => commOK 276 9 511 (getS SHB j) (CertificateChecks.KernelCo3T.DE 1))) = true := by
  quickRfl

end CFSG.KD.Co3Cent

end
