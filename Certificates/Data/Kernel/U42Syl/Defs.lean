module

public import Certificates.Data.Kernel.Sp62W.Defs

public section

namespace CFSG.KD.U42Syl

open CFSG.KC.Mat8P

@[expose] def lk (d : Nat) (L : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => d)
    (fun a _ ih j => Nat.rec (motive := fun _ => Nat) a (fun j' _ => ih j') j) L

@[expose] def wvP (A : List Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) oneP (fun j _ acc => mulP (lk oneP A j) acc) w

@[expose] def powP (X : Nat) (k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) X (fun _ acc => mulP acc X) k

@[expose] def all2 (f : Nat → Nat → Bool) (L : List Nat) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun L' => L'.isEmpty)
    (fun a _ ih L' => List.rec (motive := fun _ => Bool) false (fun b t _ => f a b && ih t) L') L

@[expose] def tabK (AT : List Nat) (TW TWI : List (List Nat)) (TT TI : List Nat) : Bool :=
  TT == TW.map (wvP AT) && TI == TWI.map (wvP AT) &&
    all2 (fun s t => Nat.beq (mulP s t) oneP) TT TI

@[expose] def repB (AT : List Nat) (a b R : Nat) (aw bw : List Nat) : Bool :=
  !(Nat.beq R oneP) && Nat.beq (powP R 4) oneP && Nat.beq (wvP (AT ++ [R]) aw) a &&
    Nat.beq (wvP (AT ++ [R]) bw) b

@[expose] def repK (AT AV : List Nat) (a b : Nat) (RW : List (List Nat)) (RT : List Nat)
    (AW BW : List (List Nat)) : Bool :=
  RT == RW.map (wvP AV) && RT.length == 16 && AW.length == 16 && BW.length == 16 &&
    (List.range 16).all fun i =>
      repB AT a b (lk oneP RT i) (AW.getD i []) (BW.getD i [])

@[expose] def xOf (TT TI RT : List Nat) (e : Nat) : Nat :=
  mulP (mulP (lk oneP TT (Nat.shiftRight e 6))
    (powP (lk oneP RT (Nat.land (Nat.shiftRight e 2) 15)) (Nat.land e 3)))
    (lk oneP TI (Nat.shiftRight e 6))

@[expose] def canonB (X : Nat) : Bool :=
  Nat.blt X (mulP X X) && Nat.blt X (mulP (mulP X X) X) && Nat.blt X (mulP (mulP X X) (mulP X X))

@[expose] def recB (TT TI RT : List Nat) (L : List Nat) : Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Bool) (fun p q => Nat.beq p q)
    (fun e _ ih p q => Nat.blt p (xOf TT TI RT e) && canonB (xOf TT TI RT e) &&
      ih (xOf TT TI RT e) q) L

end CFSG.KD.U42Syl
