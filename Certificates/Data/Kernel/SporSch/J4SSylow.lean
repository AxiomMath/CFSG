module

public import Certificates.Data.Kernel.SporSch.J4SCols

public section

namespace CFSG.KS.SporSch.C11

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def distinctK (E SO SOI : Nat → Nat) (n : Nat) : Bool :=
  bAnd(allN n (fun e => canonK (E e)),
  bAnd(allN n (fun i => strictB (SO i) (fun s => bAnd(Nat.blt s n, Nat.beq (SOI s) i))),
    allN n (fun i => bIf(Nat.blt (Nat.succ i) n, Nat.blt (E (SO i)) (E (SO (Nat.succ i))), true))))

@[expose] noncomputable def par11 (a : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun j acc => strictN acc (fun s => Nat.xor s (Nat.land (Nat.shiftRight a j) (nat_lit 1))))
    (nat_lit 11)

@[expose] noncomputable def ellK (a : Nat) : Nat := par11 (Nat.land a (nat_lit 300))

@[expose] noncomputable def vecK (v P : Nat) : Bool :=
  allN (nat_lit 11) (fun j => Nat.beq (par11 (Nat.land v (colK P j)))
    (Nat.land (Nat.shiftRight v j) (nat_lit 1)))

@[expose] noncomputable def injK (P : Nat) : Bool :=
  Nat.beq (foldN (nat_lit 2048) (fun c s => Nat.lor s (Nat.shiftLeft (nat_lit 1) (appK P c)))
    (nat_lit 0)) (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 2048)) (nat_lit 1))

end CFSG.KS.SporSch.C11

end
