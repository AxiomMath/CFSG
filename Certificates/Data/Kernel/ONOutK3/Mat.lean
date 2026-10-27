module

public import CFSG.Certificates.Kernel.Orders.Mat3
public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.ONK3

open CFSG.KC.Enum CFSG.KC.Ord

@[expose] noncomputable def LO : Nat := Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 23716)) (nat_lit 1)

@[expose] noncomputable def RM : Nat := Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 154)) (nat_lit 1)

@[expose] noncomputable def CI : Nat := rep1 (nat_lit 154) (nat_lit 154)

@[expose] noncomputable def ONE : Nat := rep1 (nat_lit 155) (nat_lit 154)

@[expose] noncomputable def UP : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft
      (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.sub (Nat.sub (nat_lit 154) i) (nat_lit 1))) (nat_lit 1))
      (Nat.succ (Nat.mul (nat_lit 155) i)))) (nat_lit 154)

@[expose] noncomputable def MUL (A B : Nat) : Nat := mul3s (nat_lit 154) (nat_lit 23716) LO CI RM A B

@[expose] noncomputable def VLD (X : Nat) : Bool := valid3 (nat_lit 23716) LO X

@[expose] noncomputable def M256 : Nat := Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 256)) (nat_lit 1)

@[expose] noncomputable def rowsK (F : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun t acc => strictN acc fun a => strictN (F t) fun X =>
      Nat.lor a (Nat.lor (Nat.shiftLeft (Nat.land X M256) (Nat.mul (nat_lit 154) t))
        (Nat.shiftLeft (Nat.shiftRight X (nat_lit 256)) (Nat.add (nat_lit 23716) (Nat.mul (nat_lit 154) t)))))
    (nat_lit 154)

@[expose] noncomputable def matT (KK SP : Nat → Nat) (PI : Nat) (f : Nat → Nat) : Nat :=
  MUL PI (rowsK fun t => KK (f (SP t)))

@[expose] noncomputable def lcode (l : Int) : Nat :=
  Int.rec (motive := fun _ => Nat) (fun n => Nat.mul (nat_lit 2) (Nat.pred n))
    (fun n => Nat.succ (Nat.mul (nat_lit 2) n)) l

@[expose] noncomputable def wordT (MT : Nat → Nat) (w : List Int) : Nat :=
  List.foldr (fun l acc => strictN acc fun a => MUL a (MT (lcode l))) ONE w

@[expose] noncomputable def uT (HT : Nat → Nat) (d : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun _ ih w acc => strictN (MUL acc (HT (Nat.land w (nat_lit 3)))) fun a =>
      ih (Nat.shiftRight w (nat_lit 2)) a) d

end CFSG.KC.ONK3

end
