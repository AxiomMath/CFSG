module

public import CFSG.Sporadic.SuzOddCore.InvArraysCheck
public import Certificates.Data.CFSGNative.Schreier.Refine
public import Mathlib.Data.Fintype.Card
public meta import CFSG.Sporadic.SuzOddCore.InvArraysCheck
public meta import Certificates.Data.CFSGNative.Schreier.Refine
public meta import Mathlib.Data.Fintype.Card

public section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def invNbr : Array (List Nat) := adjSearch 1782 #[b0Arr, b1Arr] invNeighbors

@[expose] def bTriple : Array (Array Nat) := #[b0Arr, b1Arr, vArr]

@[expose] def bTripleInv : Array (Array Nat) := bTriple.map (invCand 1782)

@[expose] def powA (n : Nat) (t : Array Nat) : Nat → Array Nat
  | 0 => idA n
  | k + 1 => compA n t (powA n t k)

@[expose] def tArr (i : Nat) : Array Nat :=
  powA 1782 (wordA 1782 bTriple bTripleInv (invRepWords.getD i [])) (invRepPowers.getD i 0)

@[expose] def initColour (rule : String) (t : Array Nat) : Array Nat :=
  Array.ofFn (n := 1782) fun x =>
    if rule == "fixed" then (if t[x.val]! == x.val then 1 else 0)
    else (if (invNbr[x.val]!).contains t[x.val]! then 1 else 0)

@[expose] def indivPoint (c : Array Nat) (p j : Nat) : Array Nat := c.set! p (4398046511093 + j)

@[expose] def refineStepT (t c : Array Nat) : Array Nat :=
  Array.ofFn (n := 1782) fun v =>
    sigCode (sigCode c[v.val]! [c[t[v.val]!]!]) (nbrColours invNbr c v.val)

@[expose] def refineIterT (t c : Array Nat) : Nat → Array Nat
  | 0 => c
  | k + 1 => refineStepT t (refineIterT t c k)

@[expose] def stepPoints (i : Nat) : List Nat := (invSteps.getD i []).map fun s => s.getD 0 0

@[expose] def stageColour (i : Nat) : Nat → Array Nat
  | 0 => refineIterT (tArr i) (initColour (invColorRules.getD i "") (tArr i))
      (invInitRefinements.getD i []).length
  | s + 1 => refineIterT (tArr i) (indivPoint (stageColour i s) ((stepPoints i).getD s 0) s)
      (((invSteps.getD i []).getD s []).getD 2 0)

@[expose] def classCount (c : Array Nat) (v : Nat) : Nat :=
  (Finset.univ.filter fun w : Fin 1782 => c[w.val]! = c[v]!).card

end CFSG.Sporadic.SuzOddCore
