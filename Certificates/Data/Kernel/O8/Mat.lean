module

public section

namespace CFSG.KC.O8.Mat

@[expose] def matApp (M v : Nat) : Nat :=
  (List.range 8).foldr (fun c acc => if v.testBit c then (M / 256 ^ c % 256) ^^^ acc else acc) 0

@[expose] def matMulM (A B : Nat) : Nat :=
  (List.range 8).foldr (fun c acc => matApp A (B / 256 ^ c % 256) + 256 * acc) 0

@[expose] def idCode : Nat := (List.range 8).foldr (fun c acc => 2 ^ c + 256 * acc) 0

end CFSG.KC.O8.Mat

end
