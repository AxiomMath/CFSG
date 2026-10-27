module

public import Certificates.Data.Kernel.Fi22Omega.Check
public import Certificates.Data.Kernel.Fi22.I242

public section

namespace CFSG.KC.Fi22Omega

open CFSG.KC.I242

@[expose] noncomputable def wordK (S : Nat → Nat) (w : List Nat) : Nat :=
  List.foldl (fun acc r => pc (S r) acc) pid w

@[expose] noncomputable def letA (x0 x1 i0 i1 l : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) i1 i0 (Nat.beq l (nat_lit 4)))
      x1 (Nat.beq l (nat_lit 3)))
    x0 (Nat.beq l (nat_lit 2))

@[expose] noncomputable def piOf (j k : Nat) : Nat :=
  List.getD (List.getD [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]] j [])
    k (nat_lit 0)

end CFSG.KC.Fi22Omega

end
