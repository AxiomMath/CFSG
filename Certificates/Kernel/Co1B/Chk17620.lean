module

public import Certificates.Kernel.Co1B.Data17620
public import Certificates.Kernel.Co1B.XB17591
public import Certificates.Kernel.Co1ThreeK.Letters
public import Certificates.Kernel.SporSch.Co1.ElemDag
public import Certificates.Data.Kernel.Co1BW
public import Certificates.Data.Kernel.Co1BBoundN
public import Certificates.Data.Kernel.Co1BBoundP
public import Certificates.Data.Kernel.SporSch.Co1Bfs
public import Certificates.Data.TabCo1ThreeA
public import CFSG.Certificates.Kernel.Lie.CT.Core
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Bound17620

open CFSG.KC.Co1BBoundP CFSG.KC.Co1BBoundN CFSG.KC.Co1BBound CFSG.KC.Co1BSpin CFSG.KC.Co1B
  CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KLie.CT CFSG.KS.SporSch.M24
  CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeA
open CertificateChecks.KernelCo1B.Bound17591 (XB)
open CertificateChecks.KernelSporSch.Co1Elem (AF)

@[expose] noncomputable def EK (j : Nat) : Nat := DA.M (Nat.add 87 j)

@[expose] noncomputable def XK : Nat := DA.M 94

@[expose] noncomputable def UK : Nat := DA.M 95

@[expose] noncomputable def WK : Nat := DA.M 96

@[expose] noncomputable def UI : Nat := DA.MI 95

@[expose] noncomputable def WI : Nat := DA.MI 96

@[expose] noncomputable def RS7 : List Nat := (List.range 7).map fun i => DA.M (87 + i)

@[expose] noncomputable def IS7 : List Nat := (List.range 7).map fun i => DA.MI (87 + i)

@[expose] noncomputable def RA : Nat := mulWK (mulWK (AF 1) (AF 4)) (AF 5)

@[expose] noncomputable def relOK (w : List Int) : Bool :=
  eqK (wordK RS7 IS7 w) oneK || eqK (wordK RS7 IS7 w) XK || eqK (wordK RS7 IS7 w) (powWK XK 2)

theorem kDA : dagWK DA.M DA.MI 2 97 KA.KW = true := by quickRfl

theorem kDAB : (Nat.beq (DA.M 0) (CertificateChecks.KernelCo1ThreeK.L.M 9) &&
    Nat.beq (DA.M 1) (CertificateChecks.KernelCo1ThreeK.L.M 10)) = true := by quickRfl

theorem kDAW : KA.KW.map CFSG.Sporadic.Co1Schreier.Native.decWord =
    CFSG.HardMathSupport.Dickson.I271.TabCo1.chainDerivs () ++ ext := by decide +kernel

theorem kOrd : (eqK (powWK XK 3) oneK && notB (eqK XK oneK) && eqK XK RA) = true := by quickRfl

theorem kCom : (allN 10 (fun j => eqK (mulWK XK (EK j)) (mulWK (EK j) XK)) &&
    notB (eqK (mulWK (EK 0) (EK 1)) (mulWK (EK 1) (EK 0)))) = true := by quickRfl

theorem kRel : relsS.all relOK = true := by quickRfl

theorem kCm : eqK (mulWK (mulWK UI WI) (mulWK UK WK)) XK = true := by quickRfl

theorem kT : (Nat.beq KA.T.length 3 &&
    allN 3 fun i => eqK (getL 0 KA.T i) (trK 24 (powWK XK i))) = true := by quickRfl

theorem kSpan : (Nat.beq span.length 24 && Nat.beq comb.length 24 &&
    span.all (fun s => Nat.blt s.1 12 && Nat.blt s.2 3) &&
    allN 24 (fun l => Nat.beq (vmF 24 (packL (span.map (slotKn 3 KA.T base))) (comb.getD l 0))
      (Nat.shiftLeft 1 l))) = true := by quickRfl

theorem kCFs : decide ([] :: KA.CFt = (List.range 12).map fun i =>
    storeSel 3 XB KA.T (base.take i) (base.getD i 0) (conds.getD i []) (KA.Sel.getD i [])) = true := by
  quickRfl

theorem kNs : (Nat.beq KA.CNs.length 12 && allN 12 fun i => memK XB (base.getD i 0) &&
    Nat.beq (KA.CNs.getD i []).length 9 && Nat.ble (KA.CNs.getD i []).sum (cnts.getD i 0)) = true := by
  quickRfl

end CertificateChecks.KernelCo1B.Bound17620

end
