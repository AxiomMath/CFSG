module

public import CFSG.Sporadic.Recognition.CoverRecipeSq
public import Certificates.Data.CFSGNative.ON.Data

public section

namespace CFSG.Sporadic.Recognition.ONMultiplier

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Sporadic.Recognition.CoverRecipe
open CFSG.Sporadic.ON.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native

@[expose] def letterZ (l : Fin 4 × Bool) : Int :=
  if l.2 then (l.1.val : Int) + 1 else -((l.1.val : Int) + 1)

@[expose] def ofCodes (c : List ℕ) : List (Fin 4 × Bool) :=
  c.map (fun x => (⟨x / 2 % 4, Nat.mod_lt _ (by norm_num)⟩, decide (x % 2 = 0)))

@[expose] def onRelCodes : List (List ℕ) :=
  [[5, 5],
  [1, 1, 1],
  [7, 1, 6, 0],
  [7, 7, 7, 7],
  [7, 5, 6, 5],
  [3, 1, 3, 1, 3, 1],
  [7, 7, 3, 6, 6, 1, 3, 1],
  [7, 7, 3, 6, 1, 6, 3, 1],
  [3, 3, 3, 3, 3, 3, 3, 3],
  [7, 3, 3, 3, 3, 7, 2, 2, 2, 2],
  [3, 3, 3, 1, 2, 1, 2, 1, 2, 1],
  [3, 3, 3, 0, 3, 3, 3, 0, 2, 0],
  [7, 7, 3, 3, 0, 2, 1, 3, 6, 6, 1, 2, 1, 3],
  [5, 1, 5, 1, 5, 0, 2, 5, 0, 5, 0, 5, 2, 0],
  [5, 3, 3, 0, 2, 5, 2, 0, 5, 0, 5, 0, 5, 3, 1],
  [5, 3, 1, 5, 1, 5, 1, 5, 2, 0, 5, 2, 2, 1, 3],
  [3, 3, 1, 3, 1, 3, 3, 1, 3, 1, 3, 3, 1, 3, 1],
  [5, 3, 3, 3, 1, 5, 2, 2, 5, 2, 5, 1, 5, 0, 3, 1],
  [7, 1, 5, 1, 5, 1, 5, 6, 2, 0, 5, 2, 2, 1, 3, 5, 3],
  [7, 3, 3, 3, 5, 0, 5, 0, 5, 3, 3, 3, 6, 5, 0, 5, 0, 5],
  [7, 7, 3, 5, 3, 6, 6, 3, 5, 3, 1, 3, 3, 5, 0, 2, 1, 2],
  [5, 3, 3, 3, 3, 5, 1, 3, 5, 0, 2, 5, 2, 2, 5, 3, 3, 3, 0],
  [7, 3, 3, 3, 1, 2, 2, 0, 4, 0, 4, 3, 0, 2, 2, 6, 1, 4, 1, 4],
  [7, 3, 3, 3, 1, 2, 2, 4, 0, 4, 1, 3, 0, 2, 2, 6, 4, 1, 4, 0],
  [7, 3, 3, 3, 6, 2, 0, 4, 3, 7, 0, 3, 7, 3, 1, 4, 3, 3, 3, 1],
  [7, 3, 3, 0, 2, 5, 3, 3, 3, 5, 1, 3, 3, 3, 0, 6, 5, 1, 5, 1],
  [7, 5, 3, 6, 2, 6, 2, 2, 1, 7, 2, 5, 0, 2, 1, 2, 2, 2, 5, 6, 1, 2, 2, 7, 0]]

@[expose] def onRels : List (List (Fin 4 × Bool)) := onRelCodes.map ofCodes

@[expose] def onCommCodes : Fin 4 → List (List ℕ × List ℕ)
  | 0 =>
    [([2, 0], [0, 2]), ([0], [3])]
  | 1 =>
    [([0, 3, 1], [2, 1, 2, 2])]
  | 2 =>
    [([0, 4, 1], [1, 4, 0]), ([2, 2, 4], [4, 2, 2])]
  | 3 =>
    [([2, 2, 7], [6, 3, 4, 2, 2, 7, 3, 0, 3, 3, 0, 3, 4, 3, 3, 6, 2])]

@[expose] def onCommWord (i : Fin 4) : List (Fin 4 × Bool) :=
  commWords (((onCommCodes i).map fun p => (ofCodes p.1, ofCodes p.2)))

abbrev onCover : List (List (Fin 4 × Bool)) := cover₂Words onRels onCommWord

abbrev onCover1 := restrictWords (subsetOf 4 [0, 1, 2]) onCover

@[expose] def onGenWords : Array (List Int) :=
  #[[1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 2, 1, -2, 1, -2, 1, 2, 1, 2, 2, 1, -2, 1, 2, 2, 1, 2, 1, 2, 2,
    1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, -2],
   [1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 2, 1, -2, 1, 2, 2, 1, 2, 2, 1, 2, 1,
    2, 2, 1, 2, 2, 1, 2, 1, 2, 1, -2, 1, 2, 2, 1, 2, 2, 1, 2],
   [1, 2, 1, 2, 1, -2, 1, 2, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 2, 1, 2, 1, 2,
    1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, -2, 1, -2, 1],
   [-2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, -2, 1, 2, 1, -2, 1, -2, -2, 1,
    2, 2, 1, 2, 1, 2, 2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2, 2, 1, 2]]

@[expose] def onSurjA : List Int := [4, -1, -2, 3, -2, -2, 3, -2, -1, 3, 2, 3, 4]

@[expose] def onSurjB : List Int := [-2, 3, 1, -2, 4, 2, -1, 3, 2]

@[expose] def onCheckWords : List (List Int) :=
  (onRels ++ (List.finRange 4).map fun i => (i, false) :: onCommWord i).map (·.map letterZ)

end CFSG.Sporadic.Recognition.ONMultiplier
