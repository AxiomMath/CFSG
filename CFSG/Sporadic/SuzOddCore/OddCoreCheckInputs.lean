module

public import CFSG.Sporadic.SuzOddCore.InvTCheck
public import Certificates.Data.CFSGNative.PSL3Four.Basic
public meta import CFSG.Sporadic.SuzOddCore.InvTCheck
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic

public section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.PSL3Four.Native

@[expose] def oddShape (i r : Nat) : List Nat := (invOddCoreShapes.getD i []).getD r []

@[expose] def oddWord (i r l : Nat) : List Nat := ((invOddCoreWords.getD i []).getD r []).getD l []

@[expose] def oddOrder (i r l : Nat) : Nat :=
  ((invOddCoreProductOrders.getD i []).getD r []).getD l 0

@[expose] def innerWordArr (i : Nat) (w : List Nat) : Array Nat :=
  w.foldr (fun h acc => compA 1782 (invInnerGenArrs i)[h - 1]! acc) (idA 1782)

@[expose] def xgxgArr (x g gi : Array Nat) : Array Nat :=
  compA 1782 x (compA 1782 g (compA 1782 x gi))

@[expose] def oddLineOK (i r l : Nat) : Bool :=
  let x := (invOddLineArrs i r)[l]!
  let g := innerWordArr i (oddWord i r l)
  let w := powA 1782 (xgxgArr x g (invCand 1782 g)) (oddOrder i r l / 2)
  permOK 1782 x && (oddWord i r l).all (fun h => decide (1 ≤ h ∧ h ≤ (invInnerGenArrs i).size)) &&
    isInvA 1782 g (invCand 1782 g) && eqA 1782 (compA 1782 w w) (idA 1782) &&
    !(eqA 1782 w (idA 1782))

@[expose] def oddRecordOK (i r : Nat) (E : Enum) : Bool :=
  let p := (oddShape i r).getD 0 0
  let gens := invOddGenArrs i r
  let lines := invOddLineArrs i r
  (allBelow gens.size fun k =>
      permOK 1782 gens[k]! && inM gens[k]! && commutesA gens[k]! (tArr i)) &&
    enumOK 1782 gens E && E.tabs.size == (oddShape i r).getD 1 0 &&
    (allBelow E.tabs.size fun k =>
      !(eqA 1782 (powA 1782 E.tabs[k]! p) (idA 1782)) || eqA 1782 E.tabs[k]! (idA 1782) ||
        anyBelow p fun j => anyBelow lines.size fun l =>
          eqA 1782 (powA 1782 E.tabs[k]! j) lines[l]!) &&
    allBelow lines.size fun l => oddLineOK i r l

@[expose] def oddEnum (i r : Nat) : Enum :=
  enumBFS 1782 (invOddGenArrs i r) ((oddShape i r).getD 1 0)

@[expose] def oddEntryOK (i : Nat) : Bool :=
  allBelow (invOddCoreShapes.getD i []).length fun r => oddRecordOK i r (oddEnum i r)

end CFSG.Sporadic.SuzOddCore
