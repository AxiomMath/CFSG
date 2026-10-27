module

public import Certificates.Kernel.AS81.Data
public import Certificates.Kernel.OmegaEight.NatData
public import Certificates.Data.Kernel.AS81Line
public import Certificates.Data.Kernel.MergeG
public import Certificates.Data.Kernel.MergeReplay
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3LineTests
public meta import Certificates.Kernel.Co1B.GenTri2045
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Co1B.GenTri2045

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelAS81

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.AS81 CFSG.KC.MergeG
open CFSG.KC.MergeR CertificateChecks.KernelO8

@[expose] noncomputable def GI (i : Nat) : Nat := pinvS 1120 11 (mask 11) (G i)

@[expose] noncomputable def rI (l k : Nat) : Nat := Nat.mod (pg 11 2047 (ML l) (Nat.mul 3 k)) 8

@[expose] noncomputable def rU (l k : Nat) : Nat :=
  Nat.mod (pg 11 2047 (ML l) (Nat.add (Nat.mul 3 k) 1)) 1120

@[expose] noncomputable def rV (l k : Nat) : Nat :=
  Nat.mod (pg 11 2047 (ML l) (Nat.add (Nat.mul 3 k) 2)) 1120

@[expose] noncomputable def mA (l s : Nat) : Nat :=
  nIf(Nat.beq l 0, MA0 s, nIf(Nat.beq l 1, MA1 s, nIf(Nat.beq l 2, MA2 s, MA3 s)))

@[expose] noncomputable def seg0 (s : Nat) : Bool :=
  segCG 1120 11 8 G (MC 0) 32 (MT 0) (MP 0) (mA 0) (rI 0) (rU 0) (rV 0) s

@[expose] noncomputable def seg1 (s : Nat) : Bool :=
  segCG 1120 11 8 G (MC 1) 32 (MT 1) (MP 1) (mA 1) (rI 1) (rU 1) (rV 1) s

@[expose] noncomputable def seg2 (s : Nat) : Bool :=
  segCG 1120 11 8 G (MC 2) 32 (MT 2) (MP 2) (mA 2) (rI 2) (rU 2) (rV 2) s

@[expose] noncomputable def seg3 (s : Nat) : Bool :=
  segCG 1120 11 8 G (MC 3) 32 (MT 3) (MP 3) (mA 3) (rI 3) (rU 3) (rV 3) s

end CertificateChecks.KernelAS81

#kc_slices CertificateChecks.KernelAS81.M0 CertificateChecks.KernelAS81.seg0 35
#kc_slices CertificateChecks.KernelAS81.M1 CertificateChecks.KernelAS81.seg1 35
#kc_slices CertificateChecks.KernelAS81.M2 CertificateChecks.KernelAS81.seg2 35
#kc_slices CertificateChecks.KernelAS81.M3 CertificateChecks.KernelAS81.seg3 35

namespace CertificateChecks.KernelAS81

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.AS81 CFSG.KC.MergeG
open CFSG.KC.MergeR CertificateChecks.KernelO8 CFSG.ComponentClassification.AS81.MinusLines

theorem kTab : tabK LT PR = true := by quickRfl

theorem kPair : pairK NSP NIP LT PR = true := by quickRfl

theorem kGens : gensK O G LT PR = true := by quickRfl

theorem kOnG : onGK O G LT = true := by quickRfl

theorem kCanG : allN 8 (fun i => canonK 1120 11 (mask 11) (1120 * 11) (G i)) = true := by quickRfl

theorem kPermG : allN 8 (fun i => permOK 1120 11 (mask 11) (1120 * 11) (G i) (GI i)) = true := by
  quickRfl

theorem kW0 : wordEqK 1120 11 (mask 11) (pidn 1120 11) G GI 8 lineH0Words[0]! (H 0) = true := by
  quickRfl
theorem kW1 : wordEqK 1120 11 (mask 11) (pidn 1120 11) G GI 8 lineH0Words[1]! (H 1) = true := by
  quickRfl
theorem kW2 : wordEqK 1120 11 (mask 11) (pidn 1120 11) G GI 8 lineH0Words[2]! (H 2) = true := by
  quickRfl
theorem kW3 : wordEqK 1120 11 (mask 11) (pidn 1120 11) G GI 8 lineH0Words[3]! (H 3) = true := by
  quickRfl

theorem kCanH : allN 4 (fun j => canonK 1120 11 (mask 11) (1120 * 11) (H j)) = true := by quickRfl

theorem kFix : allN 4 (fun j => Nat.beq (pg 11 2047 (H j) 0) 0) = true := by quickRfl

theorem kFT : bfsTK 1120 11 G 8 1 (FT 0) (FT 1) (FT 2) (FT 3) (FT 4) (FT 5) (FT 6) (FT 7) (FT 8) =
    true := by quickRfl

theorem kLT : labOKK 1120 11 G 8 1 (FT 5) (FT 0) (FT 6) (FT 7) (FT 8) = true := by quickRfl

theorem kFH : bfsTK 1120 11 H 4 5 (FH 0) (FH 1) (FH 2) (FH 3) (FH 4) (FH 5) (FH 6) (FH 7) (FH 8) =
    true := by quickRfl

theorem kLH : labOKK 1120 11 H 4 5 (FH 5) (FH 0) (FH 6) (FH 7) (FH 8) = true := by quickRfl

theorem kS0 : searchK 1120 11 2047 12320 8 G 0 1 (MC 0) (ML 0) = true := by quickRfl
theorem kS1 : searchK 1120 11 2047 12320 8 G 0 28 (MC 1) (ML 1) = true := by quickRfl
theorem kS2 : searchK 1120 11 2047 12320 8 G 0 32 (MC 2) (ML 2) = true := by quickRfl
theorem kS3 : searchK 1120 11 2047 12320 8 G 0 58 (MC 3) (ML 3) = true := by quickRfl

theorem kC : allN 4 (fun l => Nat.beq (MC l) 1118) = true := by quickRfl

@[expose] noncomputable def mergeParts (l x : Nat) : Bool :=
  bAnd(allN 1120 (fun y => Nat.beq (pgW 11 (mA l 0) y) (nIf(Nat.beq y x, 0, y))),
  bAnd(allN 1120 (fun j => Nat.ble (pgW 12 (MT l) j) (MC l)),
  bAnd(Nat.beq (mergeCnt 1120 11 G (MC l) 32 (MT l) (MP l) (mA l) (rI l) (rU l) (rV l))
    (timedCnt 1120 (MC l) (MT l)),
    finalC 1120 11 (MC l) 35 (MT l) (mA l))))

theorem kP0 : mergeParts 0 1 = true := by quickRfl
theorem kP1 : mergeParts 1 28 = true := by quickRfl
theorem kP2 : mergeParts 2 32 = true := by quickRfl
theorem kP3 : mergeParts 3 58 = true := by quickRfl

end CertificateChecks.KernelAS81

end
