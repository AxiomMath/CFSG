module

public import CFSG.Sporadic.HeldB.OuterCentCheckInputs
public import CFSG.Sporadic.HeldB.InnerCheckInputs
public meta import CFSG.Sporadic.HeldB.OuterCentCheckInputs
public meta import CFSG.Sporadic.HeldB.InnerCheckInputs

public section

namespace CFSG.ComponentClassification.SolMax.HeGen

open CFSG.Sporadic.HeldB CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Monster.B.Co2.Native
open CFSG.Certificates.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Th.Native

@[expose] def dArrs : Array (Array ℕ) := #[heDArr 0, heDArr 1, heDArr 2]

@[expose] def wF1 : List ℤ := [1, 1]

@[expose] def wF2 : List ℤ := [1, -3, 2, 3, 3, 1, 3]

@[expose] def wC : List ℤ := [1, -3, 1, 1, 3, 2, -3]

@[expose] def dWord (w : List ℤ) : Array ℕ := wordA 8330 dArrs (dArrs.map (invCand 8330)) w

@[expose] def f1A : Array ℕ := dWord wF1

@[expose] def f2A : Array ℕ := dWord wF2

@[expose] def cA : Array ℕ := dWord wC

@[expose] def wG0 : List ℤ := [2, 2, 1, -2, 1, 2, 1, -2, 1, 2, 2, 2, 1, -2, -2]

@[expose] def g0A : Array ℕ := wordA 8330 heABArrs (heABArrs.map (invCand 8330)) wG0

@[expose] def omega0 : ℕ := 4065

@[expose] def conjBy (g x : Array ℕ) : Array ℕ := compA 8330 (invCand 8330 g) (compA 8330 x g)

@[expose] def fP : List (Array ℕ) :=
  [conjBy g0A f1A, conjBy g0A f2A, conjBy g0A (compA 8330 f1A f2A)]

@[expose] def stabOK (s x : Array ℕ) : Bool :=
  fP.any fun y => eqA 8330 (compA 8330 s (compA 8330 x (invCand 8330 s))) y

@[expose] def heGenOuterCheck : Bool :=
  (List.range 3).all (fun j => permChk 8330 (heDArr j)) &&
    lettersOK 3 wF1 && lettersOK 3 wF2 && lettersOK 3 wC && lettersOK 2 wG0 &&
    permChk 8330 g0A &&
    eqA 8330 (compA 8330 f1A f1A) (idA 8330) && !eqA 8330 f1A (idA 8330) &&
    eqA 8330 (compA 8330 f2A f2A) (idA 8330) && !eqA 8330 f2A (idA 8330) &&
    !eqA 8330 f1A f2A && eqA 8330 (compA 8330 f1A f2A) (compA 8330 f2A f1A) &&
    eqA 8330 (compA 8330 cA (compA 8330 cA cA)) (idA 8330) && !eqA 8330 cA (idA 8330) &&
    eqA 8330 (compA 8330 cA f1A) (compA 8330 f1A cA) &&
    eqA 8330 (compA 8330 cA f2A) (compA 8330 f2A cA) &&
    !eqA 8330 (compA 8330 cA (heDArr 0)) (compA 8330 (heDArr 0) cA) &&
    g0A[0]! == omega0 &&
    (List.range 9).all (fun k => permChk 8330 (heStrong k) &&
      ((heStrong k)[0]! != 0 || fP.all fun x => stabOK (heStrong k) x)) &&
    (heDArr 2)[omega0]! != omega0

@[expose] def sigArrs : Array (Array ℕ) := heInnerSigma0.toArray

@[expose] def sWord (w : List ℤ) : Array ℕ := wordA 240 sigArrs (sigArrs.map (invCand 240)) w

@[expose] def wX5 : List ℤ := [2, 5, 9, 4]

@[expose] def x5A : Array ℕ := sWord wX5

@[expose] def wK : List (List ℤ) := [[], [2], [6]]

@[expose] def kA (w : List ℤ) : Array ℕ :=
  compA 240 (sWord w) (compA 240 x5A (invCand 240 (sWord w)))

@[expose] def kWords : List (List ℤ) :=
  [[-1, 2, 3, -2], [1, 3, 4, -1], [-5, -4, 5, 2, 1, 2, 3]]

@[expose] def heGenK : RawSchreierDatum 240 :=
  certificate (by decide) (wK.map fun w => permOrId 240 (kA w)) kWords #v[0, 1, 2] (by decide)

@[expose] def heGenInnerCheck : Bool :=
  heInnerSigma0.all (permChk 240) && lettersOK 9 wX5 && wK.all (lettersOK 9) && permChk 240 x5A &&
    wK.all (fun w => permChk 240 (sWord w) && permChk 240 (kA w)) &&
    eqA 240 (compA 240 x5A (compA 240 x5A (compA 240 x5A (compA 240 x5A x5A)))) (idA 240) &&
    !eqA 240 x5A (idA 240) && heGenK.check && heGenK.orderCertificate == 40320

end CFSG.ComponentClassification.SolMax.HeGen
