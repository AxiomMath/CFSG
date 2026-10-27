module

public section

namespace CFSG.Monster.VisCert.Native

@[expose] def actGo (rows : Array Nat) (v : Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | i + 1, acc => actGo rows v i (if v.testBit i then acc ^^^ rows[i]! else acc)

@[expose] def actRows (rows : Array Nat) (v : Nat) : Nat := actGo rows v 24 0

end CFSG.Monster.VisCert.Native
