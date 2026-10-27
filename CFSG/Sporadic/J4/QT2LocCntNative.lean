module

public import CFSG.Sporadic.J4.QT2LocNative

public section

namespace CFSG.Sporadic.J4.QT2

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT

@[expose] def zMasks : List Nat := ((orbits.getD 1 (3, [], [])).2.1).map Prod.fst

@[expose] def chkZMasks : Bool :=
  zMasks.all (fun c => decide (c < 2048) && letters.all fun ℓ => zMasks.contains (act ℓ c)) &&
    zMasks.length == 1771 && zMasks.Nodup && zMasks.contains 3 && zMasks.contains 1131 &&
    (orbits.getD 1 (3, [], [])).1 == 3

@[expose] def memEVec (T : Array (Array V2)) (evs : List V2) (M Mi : Array V2) (c : Nat) : Bool :=
  let v := frApply (frTable (mulRows (mulRows M (etaRows T 11 c)) Mi)) w0
  evs.any fun u => !(differs v u)

@[expose] def evsOf (T : Array (Array V2)) : List V2 :=
  (List.range 2048).map (etaVec (T.map frTable) 11)

@[expose] def candZ (loc inv : Array (Array V2)) (ℓ : Nat) : List Nat :=
  let T := uTab loc inv
  let evs := evsOf T
  let M := pathRows (repPaths.getD ℓ [])
  let Mi := invRows M
  zMasks.filter fun c => memEVec T evs M Mi c

@[expose] def chkCntZ (loc inv : Array (Array V2)) : Bool :=
  (candZ loc inv 1).length == 0 && (candZ loc inv 2).length == 0 &&
    (candZ loc inv 3).length == 0 && (candZ loc inv 4).length == 0 &&
    (candZ loc inv 5).length == 7 && (candZ loc inv 6).length == 1

@[expose] def locTabs : Array (Array V2) := (locMats ()).map frTable

@[expose] def rep6Vec : V2 := pathVec (repPaths.getD 6 [])

@[expose] def orb6 : VOrb := vorbit locTabs rep6Vec 28336 16

end CFSG.Sporadic.J4.QT2
