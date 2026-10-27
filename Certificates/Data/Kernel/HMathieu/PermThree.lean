module

public import Certificates.Data.Kernel.HMathieu.Bfs

public section

namespace CFSG.KC.HMathieu

@[expose] def pkL : List Nat → Nat
  | [] => 0
  | x :: xs => x + 32 * pkL xs

@[expose] noncomputable def permThreeK (E : List Nat) (y w1 w2 : Nat) : Bool :=
  E.all fun e => E.contains (pc24 y e) || E.contains (pc24 (pc24 y e) w1) ||
    E.contains (pc24 (pc24 y e) w2)

end CFSG.KC.HMathieu

end
