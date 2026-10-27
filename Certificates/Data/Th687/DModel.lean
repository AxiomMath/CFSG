module

public import Certificates.Data.Th687.GlueWords
public import Certificates.Data.CFSGNative.PSL3Four.Basic

public section

namespace CFSG.Sporadic.Th.Recog

open CFSG.CosetTable CFSG.PSL3Four.Native

@[expose] def dS : List (Fin 8) := [0, 2, 3, 4, 7, 6]

@[expose] def dLet (j : Fin 6) : Fin 8 := dS.get j

@[expose] def rdHSW : List (List (Fin 6 × Bool)) := restrictWords dS R0'

@[expose] def duSix : List (Fin 6 × Bool) := (List.replicate 6 [(2, true), (4, true)]).flatten

@[expose] def RD : List (List (Fin 6 × Bool)) := rdHSW ++ [duSix]

@[expose] def letArr : Array Tab := #[
  #[1, 0, 4, 5, 2, 3, 10, 11, 12, 13, 6, 7, 8, 9, 19, 20, 21, 22, 23, 14, 15, 16, 17, 18, 30, 31,
    32, 33, 34, 35, 24, 25, 26, 27, 28, 29, 40, 43, 41, 44, 36, 38, 45, 37, 39, 42, 47, 46, 48, 49,
    50],
  #[0, 1, 6, 3, 10, 5, 2, 15, 16, 17, 4, 20, 21, 22, 19, 7, 8, 9, 27, 14, 11, 12, 13, 33, 30, 31,
    38, 18, 39, 40, 24, 25, 41, 23, 44, 36, 35, 43, 26, 28, 29, 32, 42, 37, 34, 45, 46, 47, 48, 49,
    50],
  #[2, 4, 0, 9, 1, 13, 14, 7, 18, 3, 19, 11, 23, 5, 6, 26, 16, 25, 8, 10, 32, 21, 31, 12, 36, 17,
    15, 33, 37, 42, 40, 22, 20, 27, 43, 45, 24, 28, 41, 46, 30, 38, 29, 34, 47, 35, 39, 44, 48, 49,
    50],
  #[0, 1, 7, 3, 11, 5, 15, 2, 17, 16, 20, 4, 22, 21, 24, 6, 9, 8, 28, 30, 10, 13, 12, 34, 14, 37,
    36, 39, 18, 41, 19, 43, 40, 44, 23, 38, 26, 25, 35, 27, 32, 29, 45, 31, 33, 42, 47, 46, 48, 49,
    50],
  #[5, 3, 21, 0, 16, 1, 12, 13, 2, 15, 8, 9, 4, 20, 25, 22, 6, 7, 36, 31, 17, 10, 11, 40, 37, 14,
    44, 35, 26, 18, 43, 19, 39, 29, 32, 23, 33, 24, 34, 38, 27, 28, 47, 30, 41, 46, 42, 45, 48, 50,
    49],
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
    26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 50, 48,
    49]
]

@[expose] def letInv (_ : Unit := ()) : Array Tab := letArr.map (invTab 51)

@[expose] def wTab {m : Nat} (G GI : Array Tab) (w : List (Fin m × Bool)) : Tab :=
  w.foldr (fun l acc => comp 51 (if l.2 then G[l.1.val]! else GI[l.1.val]!) acc) (idTab 51)

@[expose] def rdCheck (_ : Unit := ()) : Bool :=
  let GI := letInv ()
  RD.all fun w => wTab letArr GI w == idTab 51

@[expose] def tConjCheck (_ : Unit := ()) : Bool :=
  let GI := letInv ()
  (List.finRange 6).all fun j =>
    comp 51 (comp 51 letArr[j.val]! letArr[5]!) GI[j.val]! ==
      if j.val == 4 then GI[5]! else letArr[5]!

@[expose] def dEnum (_ : Unit := ()) : Enum := enumBFS 51 letArr 3456

@[expose] def sqTabs (_ : Unit := ()) : List Tab :=
  (dEnum ()).tabs.toList.filter fun x => comp 51 x x == idTab 51

@[expose] def primeReps : List (List (Fin 6 × Bool)) := [
  [(0, true)],
  [(1, true)],
  [(2, true), (4, false), (2, true), (4, true)],
  [(4, false), (2, true), (4, true), (2, true), (3, true), (2, true)],
  [(3, true), (2, true)],
  [(2, true), (4, false), (2, true), (4, true), (2, true)],
  [(5, false)],
  [(2, true), (4, false), (5, true), (2, true), (4, true)],
  [(4, false), (5, true), (2, true), (4, true), (2, true), (3, true), (2, true)],
  [(5, false), (3, true), (2, true)],
  [(4, false), (5, true), (3, true), (2, true), (4, true)],
  [(4, true), (2, true), (4, false), (2, true), (4, false), (2, true), (1, true), (0, true)]
]

@[expose] def primeWit : List (List (List (Fin 6 × Bool) × Nat) × Nat) := [
  ([([], 1)], 0),
  ([([], 1),
    ([(5, true), (4, true), (3, true), (2, true), (1, true), (2, true), (3, true)], 1)], 0),
  ([([], 1), ([(5, true), (4, false), (2, true), (3, true), (0, true)], 2),
    ([(5, true), (3, true), (2, true), (4, false), (0, true)], 2)], 0),
  ([([], 1), ([(4, false), (5, true)], 1),
    ([(3, true), (2, true), (4, false), (5, true), (2, true), (3, true), (2, true)], 2)], 0),
  ([([], 1), ([(5, false), (4, true), (2, true), (4, true), (3, true), (0, true)], 1),
    ([(5, false), (2, true), (4, true), (2, true), (4, true), (0, true)], 1)], 0),
  ([([], 1),
    ([(2, true), (4, false), (2, true), (1, true), (2, true), (4, false), (2, true)], 1)], 0),
  ([([], 2)], 1),
  ([([], 1), ([(2, true), (3, true), (2, true)], 1)], 1),
  ([([], 1), ([(4, false), (2, true), (4, true)], 1)], 1),
  ([([], 1), ([(4, false), (3, true), (2, true), (4, true), (3, true)], 1)], 1),
  ([([], 1), ([(2, true), (1, true), (2, true), (4, true), (2, true), (4, true)], 1)], 1),
  ([([], 1),
    ([(2, true), (1, true), (2, true), (4, true), (2, true), (4, false), (0, true)], 1)], 0)
]

@[expose] def primeOrbs (_ : Unit := ()) : Array Enum :=
  let GI := letInv ()
  (primeReps.map fun r => orbitBFS 51 letArr GI (wTab letArr GI r) 3456).toArray

@[expose] def targetTab (GI : Array Tab) (i : Nat) : Tab :=
  if i == 0 then letArr[0]! else if i == 1 then letArr[5]! else GI[5]!

@[expose] def kerProd (GI : Array Tab) (x : Tab) (L : List (List (Fin 6 × Bool) × Nat)) : Tab :=
  L.foldr (fun ck acc =>
    comp 51 (comp 51 (comp 51 (wTab letArr GI ck.1) (if ck.2 == 2 then comp 51 x x else x))
      (wTab letArr GI (FreeGroup.invRev ck.1))) acc) (idTab 51)

@[expose] def kerWitOK (GI : Array Tab) (x : Tab)
    (e : List (List (Fin 6 × Bool) × Nat) × Nat) : Bool :=
  kerProd GI x e.1 == targetTab GI e.2

@[expose] def kerCheck (_ : Unit := ()) : Bool :=
  let GI := letInv ()
  let E := dEnum ()
  let O := primeOrbs ()
  let idxs := O.map fun o => indexOf o.tabs
  allBelow 12 (fun r =>
      let x := wTab letArr GI (primeReps.getD r [])
      orbitOK 51 letArr GI x O[r]! && kerWitOK GI x (primeWit.getD r ([], 0))) &&
    allBelow E.tabs.size fun i =>
      let x := E.tabs[i]!
      x == idTab 51 || (!(comp 51 x x == idTab 51) && !(comp 51 x (comp 51 x x) == idTab 51)) ||
        anyBelow 12 fun r => found idxs[r]! O[r]!.tabs x

end CFSG.Sporadic.Th.Recog
