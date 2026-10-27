module

public import CFSG.Sporadic.J4.QTData

public section

namespace CFSG.Sporadic.J4.QT

@[expose] def rowsXor (r : Nat → Nat) (m c : Nat) : Nat :=
  (List.range m).foldl (fun acc j => if c.testBit j then acc ^^^ r j else acc) 0

@[expose] def letterRow (ℓ : Int) (j : Nat) : Nat :=
  (letterRows.getD (letters.idxOf ℓ) []).getD j 0

@[expose] def act (ℓ : Int) (c : Nat) : Nat := rowsXor (letterRow ℓ) 11 c

@[expose] def sgRow (i j : Nat) : Nat := (sgRows.getD i []).getD j 0

@[expose] def actS (i c : Nat) : Nat := rowsXor (sgRow i) 11 c

end CFSG.Sporadic.J4.QT
