module

public import Certificates.Data.Kernel.BfsPin

public section

namespace CFSG.KC.BfsPin

open CFSG.KC.Enum CFSG.KS
open CFSG.KLie.CT (orN pw2 maskN)

@[expose] noncomputable def keyK (n w : Nat) (ps : List Nat) (t : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun p _ acc => Nat.add (pg w (mask w) t p) (Nat.mul n acc)) ps

@[expose] noncomputable def keysRun (n w : Nat) (ps : List Nat) (N : Nat) (T : Nat → Nat) :
    List Nat → Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun s _ ih lo acc => strictN (keyK n w ps (T s)) fun key =>
      nIf(bAnd(Nat.blt s N, Nat.ble lo key), ih (Nat.succ key) (Nat.lor acc (pw2 s)), nat_lit 0))

@[expose] noncomputable def keysSK (n w : Nat) (ps : List Nat) (N : Nat) (T : Nat → Nat) (SK : List Nat) :
    Bool :=
  bAnd(Nat.beq SK.length N, bAnd(Nat.blt (nat_lit 0) N,
    Nat.beq (keysRun n w ps N T SK (nat_lit 0) (nat_lit 0)) (maskN N)))

end CFSG.KC.BfsPin

end
