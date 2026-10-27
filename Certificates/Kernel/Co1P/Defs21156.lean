module

public import Certificates.Kernel.Co1P.Chk21158
public import Certificates.Kernel.Co1P.PinEDefs
public import Certificates.Kernel.Co1P.Pin21156
public import Certificates.Data.Kernel.Co1PLoop

public section

namespace CertificateChecks.KernelCo1P

open CFSG.KC.Co1B CFSG.KC.Co1P CFSG.KC.Co1F2 CFSG.KD.Co1P CFSG.KLie.CT CFSG.KC.TreeK
  CFSG.Sporadic.Co1Patterson.Native

@[expose] noncomputable def GE : List Nat := gensKe.map fun j => getL oneK GDS (j - 1)

@[expose] noncomputable def GEI : List Nat := gensKe.map fun j => getL oneK GDIS (j - 1)

@[expose] noncomputable def ptsGE (R : Nat) (ms : List Nat) : List Nat :=
  conjL R (treePts (hsAct GE) 6 oneK (recsT ms)).1 (treePts (hisAct GEI) 6 oneK (recsT ms)).1

@[expose] noncomputable def LP : List Nat :=
  ptsGE (ptE 202) loc202Masks ++ ptsGE (ptE 2348) loc2348Masks ++ ptsGE (ptE 3940) loc3940Masks

@[expose] noncomputable def TP : List Nat := ptsGE (ptE 35) t192Masks

@[expose] noncomputable def sortedOK (d : Nat) (xs : List Nat) : Bool := andB (sincK xs) (treeAll d xs)

@[expose] noncomputable def pinsOK : Bool :=
  andB (andB (sortedOK 9 SLP) (sortedOK 8 STP))
    (andB (eqLK SLP (sortP 9 (modL LP))) (eqLK STP (sortP 8 (modL TP))))

@[expose] noncomputable def keyK (X : Nat) : Nat := Nat.mod X (Nat.shiftLeft 1 576)

@[expose] noncomputable def locK (U t ti r ri w : Nat) : Bool :=
  (fun A E W Wi => (fun Wv => andB (eqK (mulWK (mulWK t A) ti) E) (andB (eqK (mulWK (mulWK t E) ti) A)
    (andB (eqK (mulWK (mulWK t U) ti) U) (andB (eqK (mulWK t Wv) (mulWK Wv t))
    (andB (eqK (mulWK (mulWK r A) ri) E) (andB (eqK (mulWK (mulWK r E) ri) U)
    (andB (eqK (mulWK (mulWK r U) ri) A) (andB (eqK (mulWK r Wv) (mulWK Wv r))
    (andB (memQ (mulWK (mulWK Wi A) W)) (andB (memQ (mulWK (mulWK Wi E) W))
      (memQ (mulWK (mulWK Wi U) W)))))))))))) (mulWK (mulWK W A) Wi))
    AL (repK 1) (mulWK (hsW orbQMasks w) (repXK 0)) (mulWK (repXiK 0) (hisW orbQMasks w))

@[expose] noncomputable def triSmallK : Bool :=
  (fun S Si E => andB (andB (eqK (mulWK (mulWK S AL) Si) E) (eqK (mulWK (mulWK S E) Si) AL))
    (andB (GE.all fun g => andB (eqK (mulWK g AL) (mulWK AL g)) (eqK (mulWK g E) (mulWK E g)))
    (andB (eqK (mulWK (mulWK Si (ptPE 35)) S) (ptPE 9987))
    (andB (locK (ptPE 202) (getL oneK GDS 177) (getL oneK GDIS 177) (getL oneK GDS 179)
        (getL oneK GDIS 179) 128)
      (andB (locK (ptPE 2348) (getL oneK GDS 178) (getL oneK GDIS 178) (getL oneK GDS 180)
        (getL oneK GDIS 180) 128)
      (locK (ptPE 3940) (getL oneK GDS 175) (getL oneK GDIS 175) (getL oneK GDS 181)
        (getL oneK GDIS 181) 64))))))
    (getL oneK GDS 175) (getL oneK GDIS 175) (repK 1)

@[expose] noncomputable def triAtW (TL TT : KT) (k : Nat) : Bool :=
  (fun P => orB (notB (memE (mulWK (mulWK (repXiK 1) P) (repXK 1))))
    (orB (memKT (keyK P) TL) (memKT (keyK P) TT))) (ptPE k)

@[expose] noncomputable def triChunk (c : Nat) : Bool :=
  chunkK 12600 (triAtW (treeOf 9 SLP) (treeOf 8 STP)) c

@[expose] noncomputable def triConeK : Bool :=
  (fun TL Vc => andB (memE (mulWK (mulWK (repXiK 1) Vc) (repXK 1)))
    (andB (memE (mulWK (mulWK (mulWK (repXiK 1) (hisE 35)) Vc) (mulWK (hsE 35) (repXK 1))))
    (andB (memKT (keyK Vc) TL)
    (andB (memKT (keyK (mulWK (mulWK (hisE 35) Vc) (hsE 35))) TL)
      (memKT (keyK (mulWK (mulWK (mulWK (hisE 9987) (getL oneK GDIS 175)) Vc)
        (mulWK (getL oneK GDS 175) (hsE 9987)))) TL)))))
    (treeOf 9 SLP) (ptPE 202)

end CertificateChecks.KernelCo1P

end
