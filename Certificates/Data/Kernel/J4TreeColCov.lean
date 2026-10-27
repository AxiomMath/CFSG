module

public import Certificates.Data.Kernel.J4TreeCol

public section

namespace CFSG.KC.J4TreeCol

open CFSG.J4Tree.Native

@[expose] def tileOK : List (Nat × Nat) → Nat → Nat → Bool
  | [], t, N => t == N
  | q :: l, t, N => q.1 == t && tileOK l (t + q.2) N

@[expose] def itemsOf (L : List (List Nat)) (j : Nat) : List (Nat × Nat) :=
  L.filterMap fun x => if x.getD 0 0 = j then some (x.getD 1 0, x.getD 2 0) else none

@[expose] def nPairs (D : CRec) : Nat :=
  2 ^ (treeWv D.k).length * (2 ^ (treeWv D.k).length + 1) / 2

@[expose] def covOK (R : Nat → CRec) (it : Nat → List Nat) (np nn : Nat) : Bool :=
  let L := (List.range np).map it
  (List.range nn).all fun j => (R j).mode != 1 || tileOK (itemsOf L j) 0 (nPairs (R j))

end CFSG.KC.J4TreeCol

end
