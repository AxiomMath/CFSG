module

public import Certificates.Data.Kernel.Fi23Q.Defs

public section

namespace CFSG.KC.Fi23Q

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Pc3

@[expose] noncomputable def imgV (H : Nat → Nat) (n v x : Nat) : Nat := wv H (nwR n v) x

@[expose] noncomputable def allL (L : List Nat) (f : Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => bAnd(f x, ih)) L

@[expose] noncomputable def notInN (x : Nat) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun y _ ih => bAnd(not (Nat.beq x y), ih)) L

@[expose] noncomputable def nodupN (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x t ih => bAnd(notInN x t, ih)) L

@[expose] noncomputable def fixL (H : Nat → Nat) (n p : Nat) (R : List (Nat × List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun l _ ih => bAnd(allL l.2 fun v => Nat.beq (imgV H n v p) p, ih)) R

@[expose] noncomputable def chainB (H : Nat → Nat) (n : Nat) (Ls : List (Nat × List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun l R ih => bAnd(Nat.blt l.1 (nat_lit 31671), bAnd(allL l.2 (vecOK n),
      bAnd(nodupN (l.2.map fun v => imgV H n v l.1), bAnd(fixL H n l.1 R, ih))))) Ls

end CFSG.KC.Fi23Q

end
