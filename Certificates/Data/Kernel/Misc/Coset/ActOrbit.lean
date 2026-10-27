module

public import Certificates.Data.Kernel.Misc.Coset.Act

public section

namespace CFSG.KC.MiscCoset.Act

@[expose] noncomputable def memB (c : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ ih => Bool.rec ih true (Nat.beq a c)) l

@[expose] noncomputable def forceB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def bitB (s q : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight s q) 1) 1

@[expose] noncomputable def lvFix (A : Nat → Nat) (L : Nat) (J bs : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun c _ ih => andB (Nat.blt c L) (andB (List.rec (motive := fun _ => Bool) true
      (fun b _ ih2 => andB (Nat.beq (step A L b c) b) ih2) bs) ih)) J

@[expose] noncomputable def recOK (A : Nat → Nat) (L N : Nat) (J : List Nat) (O : List Nat) :
    Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun e _ ih s => forceB (A e) fun p => andB (memB (Nat.mod e L) J)
      (andB (bitB s (Nat.div e L)) (andB (Nat.blt p N) (andB (notB (bitB s p))
        (forceB (Nat.lor s (Nat.shiftLeft 1 p)) ih))))) O

@[expose] noncomputable def levelsOK (A : Nat → Nat) (L N : Nat)
    (levels : List (Nat × List Nat × List Nat)) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
    (fun l _ ih bs => andB (Nat.blt l.1 N) (andB (lvFix A L l.2.1 bs)
      (andB (recOK A L N l.2.1 l.2.2 (Nat.shiftLeft 1 l.1)) (ih (l.1 :: bs))))) levels

@[expose] noncomputable def rowsOK (A : Nat → Nat) (L : Nat) (B : Nat → Nat) (M : Nat)
    (ws : List (List Nat)) (x : Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun w _ ih k => andB (Nat.beq (walk A L w x) (B (Nat.add (Nat.mul x M) k)))
      (ih (Nat.succ k))) ws

end CFSG.KC.MiscCoset.Act

end
