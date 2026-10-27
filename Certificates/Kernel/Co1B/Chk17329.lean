module

public import Certificates.Kernel.Co1B.Data17329
public import Certificates.Kernel.Co1B.XB17591
public import Certificates.Kernel.Co1B.Vecs
public import Certificates.Kernel.Co1ThreeK.Letters
public import Certificates.Data.Kernel.Co1BW
public import Certificates.Data.Kernel.Co1BFixImp
public import Certificates.Data.Kernel.Co1BBoundN
public import Certificates.Data.Kernel.Co1BBoundP
public import Certificates.Data.Kernel.SporSch.Co1Bfs
public import Certificates.Data.TabCo1ThreeC
public import CFSG.Certificates.Kernel.Lie.CT.Core
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Bound17329

open CFSG.KC.Co1BBoundP CFSG.KC.Co1BBoundN CFSG.KC.Co1BBound CFSG.KC.Co1BSpin CFSG.KC.Co1B
  CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KLie.CT CFSG.KS.SporSch.M24
  CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeC
open CertificateChecks.KernelCo1B.Bound17591 (XB)

@[expose] noncomputable def XK : Nat := CertificateChecks.KernelCo1ThreeK.R.M 0
@[expose] noncomputable def XT : Nat := trK 24 XK
@[expose] noncomputable def Q1K : Nat := DF.M 87
@[expose] noncomputable def Q2K : Nat := DF.M 88
@[expose] noncomputable def Q3K : Nat := DF.M 89
@[expose] noncomputable def Q4K : Nat := DF.M 90
@[expose] noncomputable def Q1I : Nat := DF.MI 87
@[expose] noncomputable def Q2I : Nat := DF.MI 88

@[expose] noncomputable def QM (l : Nat) : Nat := DF.M (Nat.add 87 l)

@[expose] noncomputable def QTs : List Nat := [trK 24 Q1K, trK 24 Q2K, trK 24 Q3K, trK 24 Q4K]

@[expose] noncomputable def ch17329fx (n : Nat) : Bool :=
  fixImpTabK XT QTs (fun j => CertificateChecks.KernelCo1B.CV.F (Nat.add (Nat.mul 13 n) j)) 13

theorem kDF : dagWK DF.M DF.MI 2 91 KF.KW = true := by quickRfl

theorem kDFB : (Nat.beq (DF.M 0) (CertificateChecks.KernelCo1ThreeK.L.M 9) &&
    Nat.beq (DF.M 1) (CertificateChecks.KernelCo1ThreeK.L.M 10)) = true := by quickRfl

theorem kDFW : KF.KW.map CFSG.Sporadic.Co1Schreier.Native.decWord =
    CFSG.HardMathSupport.Dickson.I271.TabCo1.chainDerivs () ++ ext := by decide +kernel

theorem kSmall : (eqK (powWK XK 3) oneK && notB (eqK XK oneK) &&
    eqK XK (mulWK (mulWK Q1K Q2K) (mulWK Q1I Q2I)) &&
    eqK (mulWK XK Q1K) (mulWK Q1K XK) && eqK (mulWK XK Q2K) (mulWK Q2K XK) &&
    eqK (mulWK XK Q3K) (mulWK Q3K XK) && eqK (mulWK XK Q4K) (mulWK Q4K XK)) = true := by
  quickRfl

theorem kQ : (gtPinK QM 4 300 QT.N QT.P QT.PAR QT.LAB QT.W QT.S && Nat.beq QT.N 243) = true := by
  quickRfl

theorem kBF : allN 6 (fun i => andB (memK XB (base.getD i 0))
    (Nat.beq (vmF 24 XT (base.getD i 0)) (base.getD i 0))) = true := by quickRfl

theorem kT : (Nat.beq KF.T.length 3 &&
    allN 3 fun i => eqK (getL 0 KF.T i) (trK 24 (powWK XK i))) = true := by quickRfl

theorem kT2 : (Nat.beq KF.T2.length 243 &&
    allN 243 fun i => eqK (getL 0 KF.T2 i) (trK 24 (QT.P i))) = true := by quickRfl

theorem kSpan : (Nat.beq span.length 24 && Nat.beq comb.length 24 &&
    span.all (fun s => Nat.blt s.1 15 && Nat.blt s.2 3) &&
    allN 24 (fun l => Nat.beq (vmF 24 (packL (span.map (slotKn 3 KF.T base))) (comb.getD l 0))
      (Nat.shiftLeft 1 l))) = true := by quickRfl

theorem kSpan2 : (Nat.beq span2.length 24 && Nat.beq comb2.length 24 &&
    span2.all (fun s => Nat.blt s.1 6 && Nat.blt s.2 243) &&
    allN 24 (fun l => Nat.beq (vmF 24 (packL (span2.map (slotKn 243 KF.T2 base2)))
      (comb2.getD l 0)) (Nat.shiftLeft 1 l))) = true := by quickRfl

theorem kCFs : decide (CFs1 = (List.range 15).map fun i =>
    storeSel 3 XB KF.T (base.take i) (base.getD i 0) (conds.getD i []) (KF.Sel.getD i [])) =
    true := by
  quickRfl

theorem kCFs2 : decide (KF.CFs2 = (List.range 6).map fun i =>
    storeSel 243 XB KF.T2 (base2.take i) (base2.getD i 0) (conds2.getD i []) (KF.Sel2.getD i [])) =
    true := by
  quickRfl

theorem kNs : (Nat.beq KF.CNs.length 15 && allN 15 fun i => memK XB (base.getD i 0) &&
    Nat.beq (KF.CNs.getD i []).length 9 && Nat.ble (KF.CNs.getD i []).sum (cnts.getD i 0)) =
    true := by
  quickRfl

theorem kNs2 : (Nat.beq KF.CNs2.length 6 && allN 6 fun i => memK XB (base2.getD i 0) &&
    Nat.beq (KF.CNs2.getD i []).length 9 && Nat.ble (KF.CNs2.getD i []).sum (cnts2.getD i 0)) =
    true := by
  quickRfl

theorem negSmall : notB (eqK XK (mulWK (mulWK Q2K Q1K) (mulWK Q1I Q2I))) = true := by quickRfl

theorem negQ : notB (gtPinK QM 4 300 (QT.N - 1) QT.P QT.PAR QT.LAB QT.W QT.S) = true := by
  quickRfl

theorem negFix : notB (fixImpTabK (trK 24 oneK) [trK 24 Q1K]
    (fun j => CertificateChecks.KernelCo1B.CV.F j) 117) = true := by quickRfl

theorem negBF : notB (Nat.beq (vmF 24 XT (base.getD 7 0)) (base.getD 7 0)) = true := by quickRfl

theorem negT2 : notB (eqK (getL 0 KF.T2 1) (trK 24 (QT.P 2))) = true := by quickRfl

theorem negNs2 : notB (Nat.ble (KF.CNs2.getD 0 []).sum (cnts2.getD 0 0 - 1)) = true := by quickRfl

end CertificateChecks.KernelCo1B.Bound17329

#kc_each CertificateChecks.KernelCo1B.Bound17329.ch17329fx 0 9

end
