module

public import Certificates.Data.CFSGNative.Schreier.SetOrbit
public import Std.Data.HashSet

public section

namespace CFSG.Sporadic.Schreier.Co3.Native

open CFSG.Certificates.Native

@[expose] def setKey (l : List Nat) : Nat := l.foldl (fun acc p => acc ||| (1 <<< p)) 0

@[expose] def hashSearch (gens : Array (Array Nat)) (start : List Nat) (bound : Nat) :
    Array (List Nat) × Array Nat × Array Nat := Id.run do
  let mut sets : Array (List Nat) := #[start]
  let mut par : Array Nat := #[0]
  let mut lab : Array Nat := #[0]
  let mut seen : Std.HashSet Nat := (∅ : Std.HashSet Nat).insert (setKey start)
  let mut head := 0
  for _ in [0:bound] do
    if head < sets.size && sets.size < bound then
      let s := sets[head]!
      for k in [0:gens.size] do
        if sets.size < bound then
          let t := imgSorted gens[k]! s
          let key := setKey t
          if !(seen.contains key) then
            seen := seen.insert key
            sets := sets.push t
            par := par.push head
            lab := lab.push k
      head := head + 1
  return (sets, par, lab)

@[expose] def strictlyIncreasing : List Nat → Bool
  | a :: b :: l => decide (a < b) && strictlyIncreasing (b :: l)
  | _ => true

@[expose] def sortedKeys (sets : Array (List Nat)) : List Nat :=
  (sets.toList.map setKey).mergeSort fun a b => decide (a ≤ b)

@[expose] def keysSortedOK (sets : Array (List Nat)) : Bool := strictlyIncreasing (sortedKeys sets)

end CFSG.Sporadic.Schreier.Co3.Native
