module

public import CFSG.Sporadic.ONOddCore.NonextPayload
public import CFSG.Sporadic.ONOddCore.LiftHomCheck
public import CFSG.Sporadic.Schreier.ONCheckR3E
public meta import CFSG.Sporadic.ONOddCore.NonextPayload
public meta import CFSG.Sporadic.ONOddCore.LiftHomCheck
public meta import CFSG.Sporadic.Schreier.ONCheckR3E

public section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native

@[expose] def lettersOK (k : Nat) (w : List Nat) : Bool := w.all fun l => 1 ≤ l && l ≤ k

@[expose] def conjArr (y yi x : Array Nat) : Array Nat := pcomp nPts y (pcomp nPts x yi)

@[expose] def cConj (x : Array Nat) : Array Nat := conjArr cArr (pinvCand nPts cArr) x

@[expose] def ambArrs (hA : Array (Array Nat)) : Array (Array Nat) := hA ++ hA.map cConj

@[expose] def auxOK (hA : Array (Array Nat)) (W : NonextWords) : Bool :=
  lettersOK 3 W.tWord && peq nPts (posArr nPts hA W.tWord) tArr &&
    lettersOK 3 W.vWord && peq nPts (posArr nPts hA W.vWord) vArr &&
    (List.range 4).all fun i =>
      lettersOK 3 (W.dWords.getD i []) && lettersOK 3 (W.dcWords.getD i []) &&
        peq nPts (posArr nPts hA (W.dWords.getD i [])) (wordArrs Data.intersectionWords)[i]! &&
        peq nPts (posArr nPts hA (W.dcWords.getD i [])) dConj[i]!

@[expose] def deltaImgs (b b' : Array (Array Nat)) (d di u ui bv bvi : Array Nat) (ε : Bool) :
    Array (Array Nat) :=
  b.map (conjArr di d) ++ b'.map fun a => cConj (conjArr u ui (if ε then conjArr bv bvi a else a))

@[expose] def exclOK (hA : Array (Array Nat)) (L : List LiftEntry) (W : NonextWords)
    (rel : List Nat) (x : ExclRec) : Bool :=
  let b := liftArrs hA (L.getD x.index default)
  let b' := liftArrs hA (L.getD x.second default)
  let d := posArr nPts hA x.normWord
  let di := pinvCand nPts d
  let u := posArr nPts hA x.conjWord
  let ui := pinvCand nPts u
  let bv := posArr nPts b' W.vWord
  let bvi := pinvCand nPts bv
  lettersOK 3 x.normWord && lettersOK 3 x.conjWord && decide (x.second < L.length) &&
    pisInv nPts d di && pisInv nPts u ui && pisInv nPts bv bvi &&
    peq nPts (conjArr d di tArr) (posArr nPts b W.tWord) &&
    ((List.range 4).all fun i =>
      peq nPts (conjArr u ui (posArr nPts b' (W.dcWords.getD i [])))
        (conjArr (pinvCand nPts cArr) cArr (conjArr di d (posArr nPts b (W.dWords.getD i []))))) &&
    [false, true].all fun ε => (posArr nPts (deltaImgs b b' d di u ui bv bvi ε) rel)[0]! != 0

@[expose] def innerOK (hA : Array (Array Nat)) (L : List LiftEntry) (y : InnerRec) : Bool :=
  let b := posArr nPts hA y.conjWord
  let bi := pinvCand nPts b
  lettersOK 3 y.conjWord && pisInv nPts b bi &&
    (List.range 3).all fun i =>
      peq nPts (conjArr b bi hA[i]!) (liftArrs hA (L.getD y.index default))[i]!

@[noinline, expose] def nonextOK (hA : Array (Array Nat)) (L : List LiftEntry) (C : NonextCert)
    (W : NonextWords) : Bool :=
  auxOK hA W && lettersOK 6 C.relationWord &&
    peq nPts (posArr nPts (ambArrs hA) C.relationWord) (pid nPts) &&
    C.excluded.all (exclOK hA L W C.relationWord) && C.inner.all (innerOK hA L)

end CFSG.Sporadic.ONOddCore
