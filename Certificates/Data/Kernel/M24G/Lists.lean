module

public section

namespace CFSG.KC.M24G

@[expose] def insN (a : Nat) : List Nat → List Nat
  | [] => [a]
  | b :: l => if a ≤ b then a :: b :: l else b :: insN a l

@[expose] def sortN : List Nat → List Nat
  | [] => []
  | b :: l => insN b (sortN l)

@[expose] def allIdx {α : Type} (g : Nat → α → Bool) : List α → Nat → Bool
  | [], _ => true
  | x :: L, i => g i x && allIdx g L (i + 1)

@[expose] def ascL : List Nat → Bool
  | a :: b :: l => decide (a < b) && ascL (b :: l)
  | _ => true

end CFSG.KC.M24G
