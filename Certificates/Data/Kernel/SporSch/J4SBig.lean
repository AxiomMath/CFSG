module

public import Certificates.Data.Kernel.J4Q.Mat

public section

namespace CFSG.KS.SporSch.J4B

open CFSG.KC.J4Q CFSG.KC.Loop

@[expose] noncomputable def packNK (l : List Nat) (P : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Nat → Bool)
    (fun r acc => andB (Nat.beq r (nat_lit 112)) (Nat.beq acc P))
    (fun x _ ih r acc => andB (Nat.blt x (Nat.shiftLeft (nat_lit 1) (nat_lit 112)))
      (strictB (Nat.lor acc (Nat.shiftLeft x (Nat.mul (nat_lit 128) r))) fun a => ih (Nat.succ r) a))
    l (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def letK2 (one A B3 B : Nat) (l : Int) : Nat :=
  Int.rec (motive := fun _ => Nat)
    (fun k => Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) one B3 (Nat.beq k (nat_lit 2))) A (Nat.beq k (nat_lit 1)))
    (fun k => Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) one B (Nat.beq k (nat_lit 1))) A (Nat.beq k (nat_lit 0))) l

@[expose] noncomputable def wvK (rm one A B3 B : Nat) (w : List Int) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun v => v)
    (fun l _ ih v => strictN (ih v) fun u => vecJ rm u (letK2 one A B3 B l)) w

end CFSG.KS.SporSch.J4B

end
