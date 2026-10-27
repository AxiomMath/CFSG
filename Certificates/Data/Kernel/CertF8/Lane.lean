module

public section

namespace CFSG.KC.CertF8

@[expose] noncomputable def lin (M : Nat) (P : List (Nat × Nat)) (y : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun p _ ih => Nat.xor (Nat.shiftLeft (Nat.land (Nat.shiftRight y p.1) M) p.2) ih) P

@[expose] def PX9 : List (Nat × Nat) :=
  [(0, 1), (1, 2), (2, 0), (2, 1), (3, 4), (4, 5), (5, 3), (5, 4), (6, 7), (7, 8), (8, 6), (8, 7)]

@[expose] def PS9 : List (Nat × Nat) :=
  [(0, 3), (1, 4), (2, 5), (3, 6), (4, 7), (5, 8), (6, 1), (6, 3), (7, 2), (7, 4), (8, 0), (8, 1),
    (8, 5)]

@[expose] def PF9 : List (Nat × Nat) :=
  [(0, 0), (1, 1), (2, 2), (3, 4), (3, 6), (3, 8), (4, 5), (4, 6), (5, 3), (5, 4), (5, 7), (6, 3),
    (6, 5), (6, 6), (6, 7), (7, 3), (7, 7), (7, 8), (8, 4), (8, 6), (8, 7), (8, 8)]

@[expose] def PX6 : List (Nat × Nat) :=
  [(0, 1), (1, 2), (2, 0), (2, 1), (3, 4), (4, 5), (5, 3), (5, 4)]

@[expose] def PW6 : List (Nat × Nat) :=
  [(0, 3), (1, 4), (2, 5), (3, 0), (3, 3), (4, 1), (4, 4), (5, 2), (5, 5)]

@[expose] def PF6 : List (Nat × Nat) :=
  [(0, 0), (1, 1), (1, 2), (2, 1), (3, 3), (4, 4), (4, 5), (5, 4)]

end CFSG.KC.CertF8

end
