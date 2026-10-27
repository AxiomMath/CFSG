module

public import CFSG.Sporadic.Schreier.ONCheckChain
public import CFSG.Sporadic.Schreier.ONOuterData
public meta import CFSG.Sporadic.Schreier.ONCheckChain
public meta import CFSG.Sporadic.Schreier.ONOuterData

public section

namespace CFSG.ONSchreier

open CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native

@[expose] def qonInvArrs : Array (Array Nat) := pinvs nPts qonStrongArrs

@[expose] def wordArr (w : List Int) : Array Nat := pword nPts qonStrongArrs qonInvArrs w

@[expose] def wordArrs (ws : Array (List Int)) : Array (Array Nat) :=
  pwords nPts qonStrongArrs qonInvArrs ws

@[expose] def jointArrs : Array (Array Nat) :=
  let Mg := wordArrs Data.MWords
  let c := wordArr Data.pairConjugatorWord
  Mg ++ conjAll nPts c (pinvCand nPts c) Mg

@[expose] def localChainOK (orig : Array (Array Nat)) (ch : Data.BigChain) : Bool :=
  decide (orig.size ≤ (extendStrong nPts orig ch.strongWords).size) &&
    allBelowN orig.size (fun j => peq nPts (extendStrong nPts orig ch.strongWords)[j]! orig[j]!) &&
    pointChainOK nPts orig.size (extendStrong nPts orig ch.strongWords) ch.base ch.strongWords 4 &&
    cOrbitSizes nPts (extendStrong nPts orig ch.strongWords) ch.base == ch.orbitSizes.toList

end CFSG.ONSchreier
