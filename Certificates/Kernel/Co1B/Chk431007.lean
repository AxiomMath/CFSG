module

public import Certificates.Kernel.Co1B.Data431007
public import Certificates.Kernel.Co1B.XB17591
public import Certificates.Kernel.Co1B.Vecs
public import Certificates.Kernel.Co1ThreeK.Letters
public import Certificates.Data.Kernel.Co1BW
public import Certificates.Data.Kernel.Co1BFix
public import Certificates.Data.Kernel.Co1BBoundN
public import Certificates.Data.Kernel.Co1BBoundP
public import Certificates.Data.Kernel.SporSch.Co1Bfs
public import Certificates.Data.Co1FiveRank
public import CFSG.Certificates.Kernel.Lie.CT.Core
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Bound431007

open CFSG.KC.Co1BBoundP CFSG.KC.Co1BBoundN CFSG.KC.Co1BBound CFSG.KC.Co1BSpin CFSG.KC.Co1B
  CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KLie.CT CFSG.KS.SporSch.M24
  CFSG.LocalAnalysis.GLTheoremA.H1017.Co1FiveNative
open CertificateChecks.KernelCo1B.Bound17591 (XB)

@[expose] noncomputable def KK : Nat := DF.M 87
@[expose] noncomputable def TK : Nat := DF.M 90
@[expose] noncomputable def CK : Nat := DF.M 91
@[expose] noncomputable def C2K : Nat := DF.M 92
@[expose] noncomputable def DK : Nat := DF.M 93
@[expose] noncomputable def X2K : Nat := DF.M 94

@[expose] noncomputable def FAM (l : Nat) : Nat := getL 0 [KK, DK] l
@[expose] noncomputable def EAM (l : Nat) : Nat := getL 0 [KK, DK, CK] l
@[expose] noncomputable def FBM (l : Nat) : Nat := getL 0 [KK, CK] l
@[expose] noncomputable def EBM (l : Nat) : Nat := getL 0 [KK, CK, C2K] l

@[expose] noncomputable def betaK (f₁ f₂ i : Nat) : Nat :=
  mulWK (powWK f₁ (i / 5)) (powWK f₂ (i % 5))

@[expose] noncomputable def sideK (t f₁ f₂ f₃ nfix : Nat) : Bool :=
  eqK (mulWK t t) oneK && notB (eqK t oneK) && Nat.beq (fixTabK (trK 24 t) CV.F 117) nfix &&
    eqK (mulWK t f₁) (mulWK f₁ t) && eqK (mulWK t f₂) (mulWK f₂ t) &&
    eqK (mulWK f₁ f₂) (mulWK f₂ f₁) && eqK (mulWK f₁ f₃) (mulWK f₃ f₁) &&
    eqK (mulWK f₂ f₃) (mulWK f₃ f₂)

theorem kDF : dagWK DF.M DF.MI 2 95 KF.KW = true := by quickRfl

theorem kDFB : (Nat.beq (DF.M 0) (CertificateChecks.KernelCo1ThreeK.L.M 9) &&
    Nat.beq (DF.M 1) (CertificateChecks.KernelCo1ThreeK.L.M 10)) = true := by quickRfl

theorem kDFW : KF.KW.map CFSG.Sporadic.Co1Schreier.Native.decWord =
    CFSG.HardMathSupport.Dickson.I271.TabCo1.chainDerivs () ++ ext5 := by decide +kernel

theorem kSideA : sideK TK KK DK CK 2280 = true := by quickRfl

theorem kSideB : sideK X2K KK CK C2K 0 = true := by quickRfl

theorem kFA : (gtPinK FAM 2 100 FAT.N FAT.P FAT.PAR FAT.LAB FAT.W FAT.S && Nat.beq FAT.N 25) =
    true := by quickRfl

theorem kEA : (gtPinK EAM 3 400 EAT.N EAT.P EAT.PAR EAT.LAB EAT.W EAT.S && Nat.beq EAT.N 125) =
    true := by quickRfl

theorem kFB : (gtPinK FBM 2 100 FBT.N FBT.P FBT.PAR FBT.LAB FBT.W FBT.S && Nat.beq FBT.N 25) =
    true := by quickRfl

theorem kEB : (gtPinK EBM 3 400 EBT.N EBT.P EBT.PAR EBT.LAB EBT.W EBT.S && Nat.beq EBT.N 125) =
    true := by quickRfl

theorem kTA : (Nat.beq KF.TA.length 25 &&
    allN 25 fun i => eqK (getL 0 KF.TA i) (trK 24 (betaK KK DK i))) = true := by quickRfl

theorem kTB : (Nat.beq KF.TB.length 25 &&
    allN 25 fun i => eqK (getL 0 KF.TB i) (trK 24 (betaK KK CK i))) = true := by quickRfl

theorem kSpanA : (Nat.beq spanA.length 24 && Nat.beq combA.length 24 &&
    spanA.all (fun s => Nat.blt s.1 3 && Nat.blt s.2 25) &&
    allN 24 (fun l => Nat.beq (vmF 24 (packL (spanA.map (slotKn 25 KF.TA baseA))) (combA.getD l 0))
      (Nat.shiftLeft 1 l))) = true := by quickRfl

theorem kSpanB : (Nat.beq spanB.length 24 && Nat.beq combB.length 24 &&
    spanB.all (fun s => Nat.blt s.1 3 && Nat.blt s.2 25) &&
    allN 24 (fun l => Nat.beq (vmF 24 (packL (spanB.map (slotKn 25 KF.TB baseB))) (combB.getD l 0))
      (Nat.shiftLeft 1 l))) = true := by quickRfl

theorem kCFsA : decide (KF.CFsA = (List.range 3).map fun i =>
    storeSel 25 XB KF.TA (baseA.take i) (baseA.getD i 0) (condsA.getD i []) (KF.SelA.getD i [])) =
    true := by
  quickRfl

theorem kCFsB : decide (KF.CFsB = (List.range 3).map fun i =>
    storeSel 25 XB KF.TB (baseB.take i) (baseB.getD i 0) (condsB.getD i []) (KF.SelB.getD i [])) =
    true := by
  quickRfl

theorem kNsA : (Nat.beq KF.CNsA.length 3 && allN 3 fun i => memK XB (baseA.getD i 0) &&
    Nat.beq (KF.CNsA.getD i []).length 9 && Nat.ble (KF.CNsA.getD i []).sum (cntsA.getD i 0)) =
    true := by
  quickRfl

theorem kNsB : (Nat.beq KF.CNsB.length 3 && allN 3 fun i => memK XB (baseB.getD i 0) &&
    Nat.beq (KF.CNsB.getD i []).length 9 && Nat.ble (KF.CNsB.getD i []).sum (cntsB.getD i 0)) =
    true := by
  quickRfl

end CertificateChecks.KernelCo1B.Bound431007

end
