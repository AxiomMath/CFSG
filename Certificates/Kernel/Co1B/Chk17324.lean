module

public import Certificates.Kernel.Co1B.Data17324
public import Certificates.Kernel.Co1B.XB17591
public import Certificates.Kernel.Co1ThreeK.Letters
public import Certificates.Data.Kernel.Co1BW
public import Certificates.Data.Kernel.Co1BBoundN
public import Certificates.Data.Kernel.Co1BBoundP
public import Certificates.Data.TabCo1FiveA
public import CFSG.Certificates.Kernel.Lie.CT.Core
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Bound17324

open CFSG.KC.Co1BBoundP CFSG.KC.Co1BBoundN CFSG.KC.Co1BBound CFSG.KC.Co1BSpin CFSG.KC.Co1B CFSG.KC.Co1F2
  CFSG.KC.M1F2 CFSG.KLie.CT CFSG.KS.SporSch.M24 CFSG.HardMathSupport.Dickson.I271.TabCo1FiveA
open CertificateChecks.KernelCo1B.Bound17591 (XB)

@[expose] noncomputable def KK : Nat := DA.M 87
@[expose] noncomputable def UK : Nat := DA.M 88
@[expose] noncomputable def VK : Nat := DA.M 89
@[expose] noncomputable def RS2 : List Nat := [DA.M 88, DA.M 89]
@[expose] noncomputable def IS2 : List Nat := [DA.MI 88, DA.MI 89]

theorem kDA : dagWK DA.M DA.MI 2 90 KA.KW = true := by quickRfl

theorem kDAB : (Nat.beq (DA.M 0) (CertificateChecks.KernelCo1ThreeK.L.M 9) &&
    Nat.beq (DA.M 1) (CertificateChecks.KernelCo1ThreeK.L.M 10)) = true := by quickRfl

theorem kDAW : KA.KW.map CFSG.Sporadic.Co1Schreier.Native.decWord =
    CFSG.HardMathSupport.Dickson.I271.TabCo1.chainDerivs () ++ ext := by decide +kernel

theorem kSmall : (eqK (powWK KK 5) oneK && notB (eqK KK oneK) && eqK KK KA.D0 &&
    notB (eqK UK oneK) && eqK (mulWK KK UK) (mulWK UK KK) && eqK (mulWK KK VK) (mulWK VK KK) &&
    eqK (wordK RS2 IS2 rel1) oneK && eqK (wordK RS2 IS2 rel2) oneK &&
    eqK (wordK RS2 IS2 rel3) oneK) = true := by quickRfl

theorem kT : (Nat.beq KA.T.length 5 &&
    allN 5 fun i => eqK (getL 0 KA.T i) (trK 24 (powWK KK i))) = true := by quickRfl

theorem kSpan : (Nat.beq span.length 24 && Nat.beq comb.length 24 &&
    span.all (fun s => Nat.blt s.1 6 && Nat.blt s.2 5) &&
    allN 24 (fun l => Nat.beq (vmF 24 (packL (span.map (slotKn 5 KA.T base))) (comb.getD l 0))
      (Nat.shiftLeft 1 l))) = true := by quickRfl

theorem kCFs : decide (KA.CFs = (List.range 6).map fun i =>
    storeSel 5 XB KA.T (base.take i) (base.getD i 0) (conds.getD i []) (KA.Sel.getD i [])) = true := by
  quickRfl

theorem kNs : (Nat.beq KA.CNs.length 6 && allN 6 fun i => memK XB (base.getD i 0) &&
    Nat.beq (KA.CNs.getD i []).length 9 && Nat.ble (KA.CNs.getD i []).sum (cnts.getD i 0)) = true := by
  quickRfl

end CertificateChecks.KernelCo1B.Bound17324

end
