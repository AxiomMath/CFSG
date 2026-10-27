module

public import Init

public section

namespace CFSG.OddStandard.SmallF3.Omega.Fact59Check

def popc (x : Nat) : Nat := (List.range 6).foldl (fun a i => a + (x >>> i) % 2) 0

def inD (v : Nat) : Bool := popc v == 1 || popc v == 2 || popc v == 5 || popc v == 6

def heartPair (a b : Nat) : Nat :=
  let w7 : Nat := if a == 7 || b == 7 then 1 else 0
  (List.range 6).foldl (fun acc j =>
    let wj : Nat := if a == j || b == j then 1 else 0
    acc + (((wj + w7) % 2) <<< j)) 0

end CFSG.OddStandard.SmallF3.Omega.Fact59Check
