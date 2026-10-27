module

public import CFSG.Sporadic.ONOddCore.LocalAutPayload
public import CFSG.Sporadic.ONOddCore.SigmaTriple
public import CFSG.Sporadic.ONOddCore.GraphDefs
public import CFSG.Sporadic.Schreier.ONCheckSmallAux
public meta import CFSG.Sporadic.ONOddCore.LocalAutPayload
public meta import CFSG.Sporadic.ONOddCore.SigmaTriple
public meta import CFSG.Sporadic.ONOddCore.GraphDefs
public meta import CFSG.Sporadic.Schreier.ONCheckSmallAux
public meta import Mathlib
public import Mathlib

public section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.PSL3Four.Native

@[expose] def qgArr (j : Nat) : Array Nat := localCert.quotGens.getD j #[]

@[expose] def qiArr (r : QuotRecord) (j : Nat) : Array Nat := r.images.getD j #[]

@[expose] def xWords : Array (List Nat) :=
  #[[1, 2, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2], [1, 2, 1, 2, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2],
    [1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1], [2, 2, 2, 1, 2, 2, 1, 2, 1, 1, 1, 1],
    [2, 2, 1, 2, 1, 2, 1, 1, 2, 2, 1, 2, 2], [1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1],
    [2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 1], [1, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1],
    [1, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1], [2, 1, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2],
    [1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 1],
    [2, 2, 1, 2, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2]]

@[expose] def pairGens (r : QuotRecord) : Array Tab :=
  #[dbl 120 (qgArr 0) (qiArr r 0), dbl 120 (qgArr 1) (qiArr r 1)]

@[expose] def pairRoot : Tab := dblBase 120 (Array.range 120)

@[expose] def recordCheck (idx : Std.HashMap Tab Nat) (r : QuotRecord) : Bool :=
  let E := bfs (leftStep 240 (pairGens r)) 2 pairRoot 50000
  allBelowN 2 (fun j => found idx m120Enum.tabs (pcomp 120 (pinvCand 120 Data.quotientConjugator)
    (pcomp 120 (qiArr r j) Data.quotientConjugator))) &&
    treeOK (leftStep 240 (pairGens r)) 2 pairRoot E && E.tabs.size == 40320 &&
    allBelowN 12 (fun m => peq 120 (posArr 120 #[qiArr r 0, qiArr r 1] xWords[m]!)
      (posArr 120 Data.PSL120Chain.generators (sigWord r.diag r.field r.graph m)))

@[noinline, expose] def quotCheck (idx : Std.HashMap Tab Nat) : Bool :=
  allBelowN 2 (fun j => peq 120 (qgArr j) (pcomp 120 Data.quotientConjugator
    (pcomp 120 Data.M120Chain.generators[j]! (pinvCand 120 Data.quotientConjugator)))) &&
    allBelowN 12 (fun m => peq 120 (posArr 120 #[qgArr 0, qgArr 1] xWords[m]!)
      Data.PSL120Chain.generators[m]!) &&
    xWords.all (fun w => w.all fun l => 1 ≤ l && l ≤ 2) &&
    localCert.records.all (recordCheck idx)

end CFSG.Sporadic.ONOddCore
