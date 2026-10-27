module

public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.SporCov

@[expose] noncomputable def nthR (d : Nat) (l : List Nat) (i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => d)
    (fun a _ ih j => Nat.rec (motive := fun _ => Nat) a (fun k _ => ih k) j) l i

@[expose] noncomputable def let4 (MA MAi MB MBi c : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) MBi MB (Nat.beq c (nat_lit 2)))
      MAi (Nat.beq c (nat_lit 1)))
    MA (Nat.beq c (nat_lit 0))

@[expose] noncomputable def letLn (MA MAi MB MBi ONE : Nat) (Rg : List Nat) (c : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nthR ONE Rg (Nat.sub c (nat_lit 4))) (let4 MA MAi MB MBi c)
    (Nat.blt c (nat_lit 4))

@[expose] noncomputable def mwLn (mul : Nat → Nat → Nat) (lt : Nat → Nat) (w : List Nat) (acc : Nat) :
    Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun c _ ih acc => CFSG.KC.Loop.strictN (mul (lt c) acc) ih) w acc

@[expose] noncomputable def forceR (x : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) x

@[expose] noncomputable def regR (mul : Nat → Nat → Nat) (ONE MA MAi MB MBi : Nat)
    (Ws : List (List Nat)) : (List Nat → Bool) → Bool :=
  List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun k => k List.nil)
    (fun w _ ih k => forceR (mwLn mul (let4 MA MAi MB MBi) w ONE) fun x =>
      ih fun xs => k (List.cons x xs)) Ws

@[expose] noncomputable def kitLn (mul : Nat → Nat → Nat) (ONE MA MAi MB MBi : Nat)
    (Ws : List (List Nat)) (k : (List Nat → Nat) → Bool) : Bool :=
  forceR MA fun A => forceR MAi fun Ai => forceR MB fun B => forceR MBi fun Bi =>
    Nat.beq (mul A Ai) ONE && Nat.beq (mul B Bi) ONE &&
      regR mul ONE A Ai B Bi Ws fun Rg => k fun u => mwLn mul (letLn A Ai B Bi ONE Rg) u ONE

@[expose] noncomputable def eqM (mw : List Nat → Nat) (u v : List Nat) : Bool :=
  Nat.beq (mw u) (mw v)

@[expose] noncomputable def letT (_ : Nat) : Bool := true

@[expose] noncomputable def trR (w S d X : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => Nat.add acc (Nat.land (Nat.shiftRight X (Nat.add (Nat.mul S i) (Nat.mul w i)))
      (Nat.sub (Nat.shiftLeft 1 w) 1))) d

end CFSG.KC.SporCov

end
