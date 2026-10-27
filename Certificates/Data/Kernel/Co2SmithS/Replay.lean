module

public import Init.Data.List.Basic

public section

namespace CFSG.KC.Co2SmithS

@[expose] def stepC (PA LA : Nat → Nat) (h l c a : Nat) : Nat :=
  if c = 0 then 0 else if a < c then c else if a = c ∧ PA c = h ∧ LA c = l then c + 1 else 0

@[expose] def rowC (PA LA : Nat → Nat) (TB : Nat → Nat → Nat) (ngen h c : Nat) : Nat :=
  (List.range ngen).foldl (fun c l => stepC PA LA h l c (TB h l)) c

end CFSG.KC.Co2SmithS

end
