module

public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.J4Count

@[expose] noncomputable def combo (B : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun b _ ih m => Nat.xor (nIf(Nat.testBit m (nat_lit 0), b, nat_lit 0))
      (ih (Nat.shiftRight m (nat_lit 1)))) B

@[expose] noncomputable def decode (P : List Nat) (a : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun p _ ih => Nat.add (nIf(Nat.testBit a p, nat_lit 1, nat_lit 0)) (Nat.mul (nat_lit 2) ih)) P

@[expose] def BS : List (List Nat) :=
  [[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024], [1720], [], [], [104, 315, 686, 1195],
    [2, 5, 8, 49, 64, 145, 272, 512, 1040], [2, 29, 37, 64, 384, 525, 1028]]

@[expose] def PS : List (List Nat) :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10], [10], [], [], [6, 8, 9, 10], [1, 2, 3, 5, 6, 7, 8, 9, 10],
    [1, 4, 5, 6, 8, 9, 10]]

@[expose] def CZ : List Nat := [1771, 1, 0, 0, 15, 427, 91]

end CFSG.KC.J4Count

end
