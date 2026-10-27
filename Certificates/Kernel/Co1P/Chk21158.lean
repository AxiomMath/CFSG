module

public import Certificates.Kernel.Co1P.Chk21157
public import CFSG.Sporadic.Co1Patterson.AmalgamRigidInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977Commuting
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylData
public import CFSG.Sporadic.Co1Block.Iota

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1P

open CFSG.KC.Co1B CFSG.KC.Co1P CFSG.KC.Co1F2 CFSG.KD.Co1P CFSG.KD.Co1B CFSG.KLie.CT
  CFSG.Sporadic.Co1Patterson.Native CFSG.EvenSmallLie.OmegaEight

@[expose] noncomputable def QG : List Nat := (List.range 8).map fun k => getL oneK IRS (36 + k)

@[expose] noncomputable def QL : List Nat :=
  (CFSG.KC.TreeK.treePts (hisAct QG) 8 oneK (recsT CFSG.Sporadic.Co1Block.twoAQMasks)).1

@[expose] noncomputable def memQ (X : Nat) : Bool := QL.any fun y => eqK X y

@[expose] noncomputable def qwW (e : Nat) : Nat :=
  (List.range 8).foldl (fun acc k => if e.testBit k = true then mulWK acc (getL oneK IRS (36 + k))
    else acc) oneK

@[expose] noncomputable def ypW (c : Nat) : Nat :=
  (List.range 8).foldl (fun acc i => if c.testBit i = true then
    mulWK acc (qwW (CFSG.Sporadic.Co1Patterson.TwistNative.yBits.getD i 0)) else acc) oneK

@[expose] noncomputable def qaeAt (Q P Y : Nat) : Bool :=
  orB (notB (memQ (mulWK (mulWK (repXiK 1) Y) (repXK 1))))
    (orB (eqK Y oneK) (orB (eqK Y Q) (orB (eqK Y P) (eqK Y (mulWK Q P)))))

@[expose] noncomputable def qaeK (Q P : Nat) : Bool :=
  allN 256 fun c => andB (qaeAt Q P (ypW c)) (qaeAt Q P (mulWK (ypW c) AL))

theorem treeAQ_ok :
    (CFSG.KC.TreeK.treePts (hisAct QG) 8 oneK (recsT CFSG.Sporadic.Co1Block.twoAQMasks)).2 = true := by
  quickRfl

theorem recsAQ_len : (recsT CFSG.Sporadic.Co1Block.twoAQMasks).length = 511 := by decide

theorem qae_chk : qaeK (wK 64) (wK 128) = true := by quickRfl

theorem qae_neg : notB (qaeK oneK (wK 128)) = true := by quickRfl

@[expose] noncomputable def conjEK (E : Nat) : Bool :=
  andB (andB (andB (canK E) (canK E)) (Nat.beq (mulK E E) oneK)) (allN 8 fun k =>
    (fun x => orB (eqK x (ypW (eCols.getD k 0))) (eqK x (mulWK (ypW (eCols.getD k 0)) AL)))
      (mulWK (mulWK E (qwW (CFSG.Sporadic.Co1Patterson.TwistNative.yBits.getD k 0))) E))

@[expose] noncomputable def edgeK (K0 K0i Y0 Y0i : Nat) : Bool :=
  (fun Q P E => andB (eqK (mulWK (mulWK K0 P) K0i) (mulWK Q P))
    (andB (eqK (mulWK (mulWK Y0 Q) Y0i) Q) (andB (eqK (mulWK (mulWK Y0 P) Y0i) (mulWK Q P))
      (andB (eqK Q (mulWK (ypW 217) AL)) (andB (eqK P (ypW 9)) (andB (conjEK E)
        (uBasis.all fun c => eqK (mulWK (ypW c) E) (mulWK E (ypW c))))))))) (wK 64) (wK 128) (repK 1)

theorem edge_chk : edgeK (getL oneK GDS 94) (getL oneK GDIS 94) (getL oneK GDS 92)
    (getL oneK GDIS 92) = true := by quickRfl

theorem edge_neg : notB (edgeK (getL oneK GDS 94) (getL oneK GDIS 94) (getL oneK GDS 94)
    (getL oneK GDIS 94)) = true := by quickRfl

theorem edge_small : (decide (1 ≤ y0Idx) && decide (y0Idx ≤ 190) &&
    uBasis.all (fun c => CFSG.Sporadic.Co1Patterson.TwistNative.colsApply eCols c == c) &&
    CFSG.Sporadic.Co1Patterson.TwistNative.colsApply eCols 1 == 8 &&
    CFSG.Sporadic.Co1Patterson.TwistNative.colsApply eCols 16 == 192) = true := by quickRfl

@[expose] def stabA (y : Nat) : Bool := uBasis.all (fun c => bNat y c == bNat 1 c) && qNat y == qNat 1

@[expose] def stabB (y : Nat) : Bool := uBasis.all (fun c => bNat y c == bNat 16 c) && qNat y == qNat 16

@[expose] def stabF : Bool :=
  ((List.range 256).filter stabA).all fun y₁ => ((List.range 256).filter stabB).all fun y₂ =>
    !(bNat y₁ y₂ == bNat 1 16) || (y₁ == 1 && y₂ == 16) || (y₁ == 8 && y₂ == 192)

theorem stab_chk : stabF = true := by quickRfl

theorem perp_chk : perpOK = true := by quickRfl

end CertificateChecks.KernelCo1P

end
