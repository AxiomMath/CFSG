module

public import CFSG.Sporadic.Schreier.ONCheckAux
public import CFSG.Sporadic.Schreier.ONCheckSmallAux
public meta import CFSG.Sporadic.Schreier.ONCheckAux
public meta import CFSG.Sporadic.Schreier.ONCheckSmallAux

public section

namespace CFSG.ONSchreier

open CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native CFSG.PSL3Four.Native

@[expose] def hArr : Array Nat := (wordArrs Data.MWords)[1]!

@[expose] def vArr : Array Nat := pcomp nPts (pinvCand nPts cArr) (pcomp nPts zArr cArr)

@[expose] def dhGens : Array (Array Nat) := dConj.push hArr

@[expose] def dhInv : Array (Array Nat) := pinvs nPts dhGens

@[expose] def mWordsDH : Array (List Int) := #[[1], [5], [-5, 2, 4, 4, 5, 4]]

@[expose] def hWordsDH : Array (List Int) :=
  #[[1], [5, -4, 5, 5, 3, -5, -5, 4, 2], [4, -3, -5, -3, 4, 1], [-3, 2, -5, -4, 5, 3]]

@[expose] def hGensArr : Array (Array Nat) := pwords nPts dhGens dhInv hWordsDH

@[expose] def dEnum : Enum := enumBFS nPts dConj 200

@[expose] def hEnum : Enum := enumBFS nPts hGensArr 200

@[expose] def aTabs : Array Tab :=
  dEnum.tabs.filter fun t =>
    dEnum.tabs.any fun u => u == conjTab nPts hArr (pinvCand nPts hArr) t

@[expose] def hvhvArr : Array Nat :=
  pcomp nPts (pinvCand nPts hArr)
    (pcomp nPts vArr (pcomp nPts hArr (pinvCand nPts vArr)))

@[expose] def order7Moves (c : Array Nat) : Bool :=
  (#[0, 227759, 100817] : Array Nat).any fun p =>
    (Nat.repeat (fun x => hArr[c[x]!]!) 7 p) != p

@[expose] def liftWordDH : List Int := [-5, -5, -3, 5, 5, 3]

@[expose] def mLiftArr : Array Nat := pword nPts dhGens dhInv liftWordDH

end CFSG.ONSchreier
