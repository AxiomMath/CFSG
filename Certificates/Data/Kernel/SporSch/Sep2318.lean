module

public import Certificates.Data.Kernel.SporSch.ThRows

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum

@[expose] noncomputable def sepBit (x k : Nat) : Nat := Nat.land (Nat.shiftRight x k) (nat_lit 1)

@[expose] noncomputable def sepTrK (R T : Nat → Nat) (i : Nat) : Bool :=
  allN (nat_lit 248) (fun j => Nat.beq (sepBit (T j) i) (sepBit (R i) j))

@[expose] noncomputable def sepCodeK (G : Nat → Nat) (i j : Nat) : Nat :=
  Nat.add (Nat.add (Nat.add (sepBit (G (Nat.mul (nat_lit 2) i)) (Nat.mul (nat_lit 2) j))
    (Nat.mul (nat_lit 2) (sepBit (G (Nat.mul (nat_lit 2) i)) (Nat.succ (Nat.mul (nat_lit 2) j)))))
    (Nat.mul (nat_lit 4) (sepBit (G (Nat.succ (Nat.mul (nat_lit 2) i))) (Nat.mul (nat_lit 2) j))))
    (Nat.mul (nat_lit 8)
      (sepBit (G (Nat.succ (Nat.mul (nat_lit 2) i))) (Nat.succ (Nat.mul (nat_lit 2) j))))

@[expose] noncomputable def sepWV (A BB : Nat → Nat) (w : List Int) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun z _ ih x => strictN (ih x) (fun y =>
      nIf(Nat.beq (CFSG.KS.Mathieu.icode z) (nat_lit 2), vmT A y, vmT BB y))) w x

@[expose] noncomputable def sepKeyK (A BB : Nat → Nat) (ka kb : Nat) (w : List Int) (x y : Nat) :
    Bool :=
  strictB (canonN (sepWV A BB w ka) (sepWV A BB w kb)) (fun k =>
    bAnd(Nat.beq (Nat.mod k (Nat.shiftLeft (nat_lit 1) (nat_lit 256))) x,
    bAnd(Nat.beq (Nat.div k (Nat.shiftLeft (nat_lit 1) (nat_lit 256))) y,
    bAnd(Nat.blt (nat_lit 0) x, bAnd(Nat.blt x y, bAnd(Nat.blt y (Nat.xor x y),
      Nat.blt y (Nat.shiftLeft (nat_lit 1) (nat_lit 248))))))))

@[expose] noncomputable def sepWordsK (A BB : Nat → Nat) (ka kb : Nat) (S : Nat → Nat)
    (ws : List (List Int)) (i : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun w _ ih i => bAnd(sepKeyK A BB ka kb w (S (Nat.mul (nat_lit 2) i))
      (S (Nat.succ (Nat.mul (nat_lit 2) i))), ih (Nat.succ i))) ws i

@[expose] noncomputable def sepCntN (n : Nat) (f : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun k ih => Nat.add ih (f k)) n

@[expose] noncomputable def sepTV (T : Nat → Nat) (k : Nat) : Nat := T (Nat.mul (nat_lit 2) k)

@[expose] noncomputable def sepTP (T : Nat → Nat) (k : Nat) : Nat :=
  T (Nat.succ (Nat.mul (nat_lit 2) k))

end CFSG.KS.SporSch

end
