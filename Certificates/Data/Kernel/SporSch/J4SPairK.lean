module

public import Certificates.Data.Kernel.J4Q.Mat

public section

namespace CFSG.KS.SporSch.J4B

open CFSG.KC.J4Q CFSG.KC.Loop

@[expose] noncomputable def letA (one X1 X2 Y1 Y2 : Nat) (l : Int) : Nat :=
  Int.rec (motive := fun _ => Nat)
    (fun k => Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) one Y1 (Nat.beq k (nat_lit 2))) X1 (Nat.beq k (nat_lit 1)))
    (fun k => Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) one Y2 (Nat.beq k (nat_lit 1))) X2 (Nat.beq k (nat_lit 0))) l

@[expose] noncomputable def letB (one X1 X2 Y1 Y2 : Nat) (l : Int) : Nat := letA one X2 X1 Y2 Y1 l

@[expose] noncomputable def wFK (c rm one X1 X2 Y1 Y2 : Nat) (w : List Int) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun a => a)
    (fun l _ ih a => strictN (ih a) fun t => mulJ c rm (letA one X1 X2 Y1 Y2 l) t) w

@[expose] noncomputable def wSK (c rm one X1 X2 Y1 Y2 : Nat) (w : List Int) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun b => b)
    (fun l _ ih b => strictN (ih b) fun t => mulJ c rm t (letB one X1 X2 Y1 Y2 l)) w

@[expose] noncomputable def dropI (n : Nat) (l : List Int) : List Int :=
  Nat.rec (motive := fun _ => List Int → List Int) (fun l => l)
    (fun _ ih l => ih (List.rec (motive := fun _ => List Int) List.nil (fun _ t _ => t) l)) n l

@[expose] noncomputable def takeI (n : Nat) (l : List Int) : List Int :=
  List.rec (motive := fun _ => Nat → List Int) (fun _ => List.nil)
    (fun x _ ih n => Nat.rec (motive := fun _ => List Int) List.nil (fun m _ => List.cons x (ih m)) n) l n

@[expose] noncomputable def prodFK (c rm one : Nat) (fs : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) one (fun a _ ih => strictN ih fun t => mulJ c rm a t) fs

@[expose] noncomputable def prodSK (c rm one : Nat) (ss : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) one (fun b _ ih => strictN ih fun t => mulJ c rm t b) ss

end CFSG.KS.SporSch.J4B

end
