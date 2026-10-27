
module

public import CFSG.Sporadic.Schreier.Co3OrbitZCheckBase
public meta import CFSG.Sporadic.Schreier.Co3OrbitZCheckBase

public section

namespace CFSG.Sporadic.Schreier.Co3

open CFSG.Certificates.Native CFSG.Sporadic.Schreier.Co3.Native

structure Co3Key where
  mask : Nat
deriving BEq

instance : Hashable Co3Key := ⟨fun k => UInt64.ofNat (k.mask % 18446744073709551557)⟩

@[expose] def co3KeySearch (gens : Array (Array Nat)) (start : List Nat) (bound : Nat) :
    Array (List Nat) × Array Nat × Array Nat := Id.run do
  let mut sets : Array (List Nat) := #[start]
  let mut par : Array Nat := #[0]
  let mut lab : Array Nat := #[0]
  let mut seen : Std.HashSet Co3Key := (∅ : Std.HashSet Co3Key).insert ⟨setKey start⟩
  let mut head := 0
  for _ in [0:bound] do
    if head < sets.size && sets.size < bound then
      let s := sets[head]!
      for k in [0:gens.size] do
        if sets.size < bound then
          let t := imgSorted gens[k]! s
          let key : Co3Key := ⟨setKey t⟩
          if !(seen.contains key) then
            seen := seen.insert key
            sets := sets.push t
            par := par.push head
            lab := lab.push k
      head := head + 1
  return (sets, par, lab)

@[expose] def co3OrbitT : Array (List Nat) × Array Nat × Array Nat :=
  co3KeySearch co3OrigArrs co3ItNat 2608200

end CFSG.Sporadic.Schreier.Co3
