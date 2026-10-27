module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KS.PermL

open CFSG.KC.Enum

@[expose] noncomputable def permRun (n : Nat) (l : List Nat) : Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Bool)
    (fun cnt _ => Nat.beq cnt n)
    (fun x _ ih cnt msk => bAnd(Nat.blt x n,
      bAnd(Nat.beq (Nat.land msk (Nat.shiftLeft (nat_lit 1) x)) (nat_lit 0),
        strictB (Nat.succ cnt) fun c => ih c (Nat.lor msk (Nat.shiftLeft (nat_lit 1) x)))))
    l

@[expose] noncomputable def permLK (n : Nat) (l : List Nat) : Bool :=
  permRun n l (nat_lit 0) (nat_lit 0)

end CFSG.KS.PermL

end
