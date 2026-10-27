module

public import CFSG.Certificates.PresentationLetters
public import Mathlib

public section

namespace CFSG.KC.L34Cov

open CFSG.Certificates.CosetEnumeration

@[expose] def decC (n : Nat) : Char :=
  cond (Nat.beq n 0) 'a' (cond (Nat.beq n 1) 'A' (cond (Nat.beq n 2) 'b' 'B'))

@[expose] def decL (n : Nat) : Fin 2 × Bool :=
  cond (Nat.beq n 0) (0, true) (cond (Nat.beq n 1) (0, false) (cond (Nat.beq n 2) (1, true)
    (1, false)))

@[expose] def invW (w : List Nat) : List Nat := (w.map invCode).reverse

@[expose] def substC (hs : List (List Nat)) (r : List Nat) : List Nat :=
  r.flatMap fun c => cond (Nat.beq (Nat.mod c 2) 0) (hs.getD (Nat.div c 2) [])
    (invW (hs.getD (Nat.div c 2) []))

@[expose] def codesOK (w : List Nat) : Bool := w.all fun c => Nat.blt c 4

end CFSG.KC.L34Cov

end
