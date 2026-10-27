module

public import CFSG.Sporadic.Schreier.RuArrays
public import CFSG.Certificates.NativeSetOrbit
public meta import CFSG.Sporadic.Schreier.RuArrays
public meta import CFSG.Certificates.NativeSetOrbit
public meta import CFSG.Sporadic.Schreier.RuEnum
public import CFSG.Sporadic.Schreier.RuEnum
public meta import Mathlib.GroupTheory.Schreier
public import Mathlib.GroupTheory.Schreier

public section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def ruTreeGens : Array (Array ℕ) := #[ruA0A, ruA1A]

@[expose] def ruTreePar : Array ℕ :=
  Array.ofFn (n := 593775) fun j => if j.val = 0 then 0 else ruTreeParent j.val

@[expose] def ruTreeLab : Array ℕ :=
  Array.ofFn (n := 593775) fun j => if j.val = 0 then 0 else ruTreeGen j.val

@[expose] def ruFixZ : List ℕ := fixedList 4060 ruZA

@[expose] def ruTreeSets : Array (List ℕ) := Id.run do
  let mut sets : Array (List ℕ) := Array.mkEmpty 593775
  sets := sets.push ruFixZ
  for j in [1:593775] do
    sets := sets.push (imgSorted ruTreeGens[ruTreeLab[j]!]! sets[ruTreePar[j]!]!)
  return sets

@[expose] def ruSortedStrict (sets : Array (List ℕ)) : Bool :=
  decide (List.IsChain (fun x y : List ℕ => x < y)
    (sets.toList.mergeSort fun x y => decide (x ≤ y)))

end CFSG.Sporadic.RuSchreier
