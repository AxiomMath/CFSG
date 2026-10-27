module

public import Certificates.Data.Kernel.TwistDce2.Cover

public section

namespace CFSG.KC.TwDce2

open CFSG.KC.TwDce

@[expose] noncomputable def codesW (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (wMk (nat_lit 0) (nat_lit 0))
    (fun c _ acc => TwDce.sN acc (fun a => wCat (wOne c) a)) w

@[expose] noncomputable def codesOK (w : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun c _ acc => andB (Nat.blt c (nat_lit 12)) acc) w

@[expose] noncomputable def fixAll (F : Nat → Nat) (NP w : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun x acc => andB acc (Nat.beq (evP F w x) x)) NP

@[expose] noncomputable def relsOK (F : Nat → Nat) (NP : Nat) (ws : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun w _ acc => andB (andB (codesOK w) (TwDce.sB (codesW w) (fun v => fixAll F NP v))) acc) ws

@[expose] noncomputable def fixesPt (F : Nat → Nat) (INVM : Nat) (RW : Nat → Nat) (L : List Nat)
    (p : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun c _ acc => andB (Nat.beq (evP F (gWord INVM RW c) p) p) acc) L

@[expose] noncomputable def invCodesOK (INVM m : Nat) : Bool :=
  allRange (fun i => Nat.beq (ivL INVM (Nat.mul (nat_lit 2) i))
    (Nat.add (Nat.mul (nat_lit 2) i) (nat_lit 1))) (nat_lit 0) m

end CFSG.KC.TwDce2

end
