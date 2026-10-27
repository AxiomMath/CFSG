module

public import CFSG.Sporadic.J4.QTNative
public import Certificates.Data.CFSGNative.J4.Cert

public section

namespace CFSG.Sporadic.J4.QT2

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT

@[expose] def repPaths : List (List Nat) :=
  [[], [1], [2], [1, 2], [2, 2], [2, 1, 2, 2, 2],
    [1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 2]]

@[expose] def pathVecFrom : List Nat → V2 → V2
  | [], v => v
  | l :: ls, v => pathVecFrom ls (frApply (frTable (baseMats[l - 1]?.getD idRows)) v)

@[expose] def pathVec (path : List Nat) : V2 := pathVecFrom path rootV

@[expose] def repCert (cap : Nat) : Bool :=
  let bs := bfs (frTable rowsA) (frTable rowsB) rootV cap
  (List.range 7).all fun i => (rdV2 bs.keys (subReps[i]?.getD 0)).beq (pathVec (repPaths.getD i []))

@[expose] def pathRows : List Nat → Array V2
  | [] => idRows
  | l :: ls => mulRows (baseMats[l - 1]?.getD idRows) (pathRows ls)

@[expose] def tMasks : List Nat := ((orbits.getD 0 (1, [], [])).2.1).map Prod.fst

@[expose] def chkTClosed : Bool :=
  tMasks.all fun c => letters.all fun ℓ => tMasks.contains (act ℓ c)

@[expose] def chkD (loc inv : Array (Array V2)) : Bool :=
  let T := uTab loc inv
  let F := T.map frTable
  let evs := (List.range 2048).map (etaVec F 11)
  (List.range' 1 6).all fun l =>
    let M := pathRows (repPaths.getD l [])
    let Mi := invRows M
    eqRows (mulRows M Mi) idRows &&
      tMasks.all fun c =>
        let v := frApply (frTable (mulRows (mulRows M (etaRows T 11 c)) Mi)) w0
        evs.all fun u => differs v u

end CFSG.Sporadic.J4.QT2
