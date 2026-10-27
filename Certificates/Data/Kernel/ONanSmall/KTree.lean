module

public section

namespace CFSG.KC.ONanSmall

inductive KTree (α : Type) where
  | leaf : KTree α
  | node : KTree α → α → KTree α → KTree α

namespace KTree

variable {α : Type} (key : α → Nat)

@[expose] def insert (y : α) : KTree α → KTree α
  | leaf => node leaf y leaf
  | node l x r => if key y < key x then node (insert y l) x r else node l x (insert y r)

@[expose] def ofList (L : List α) : KTree α := L.foldl (fun t y => insert key y t) leaf

@[expose] def memK [DecidableEq α] (y : α) : KTree α → Bool
  | leaf => false
  | node l x r => decide (y = x) || if key y < key x then memK y l else memK y r

@[expose] def toList : KTree α → List α
  | leaf => []
  | node l x r => toList l ++ x :: toList r

end KTree

end CFSG.KC.ONanSmall
