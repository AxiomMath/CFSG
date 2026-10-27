module

public import Certificates.Data.CFSGNative.MonsterB.Co2Chain

public section

namespace CFSG.Certificates.Native

open CFSG.Monster.B.Co2.Native

@[expose] def imgSorted (g : Array Nat) (l : List Nat) : List Nat :=
  (l.map fun p => g[p]!).mergeSort fun a b => decide (a ≤ b)

@[expose] def fixedList (n : Nat) (x : Array Nat) : List Nat :=
  (List.range n).filter fun p => x[p]! == p

@[expose] def translateSearch (gens : Array (Array Nat)) (start : List Nat) (bound : Nat) :
    Array (List Nat) × Array Nat × Array Nat := Id.run do
  let mut sets : Array (List Nat) := #[start]
  let mut par : Array Nat := #[0]
  let mut lab : Array Nat := #[0]
  let mut head := 0
  for _ in [0:bound] do
    if head < sets.size && sets.size < bound then
      let s := sets[head]!
      for k in [0:gens.size] do
        if sets.size < bound then
          let t := imgSorted gens[k]! s
          if !(sets.contains t) then
            sets := sets.push t
            par := par.push head
            lab := lab.push k
      head := head + 1
  return (sets, par, lab)

@[expose] def translatesOK (gens : Array (Array Nat)) (start : List Nat) (sets : Array (List Nat))
    (par lab : Array Nat) : Bool :=
  decide (0 < sets.size) && sets[0]! == start &&
    allLt sets.size fun k => k == 0 || (decide (par[k]! < k) && decide (lab[k]! < gens.size) &&
      sets[k]! == imgSorted gens[lab[k]!]! sets[par[k]!]!)

end CFSG.Certificates.Native
