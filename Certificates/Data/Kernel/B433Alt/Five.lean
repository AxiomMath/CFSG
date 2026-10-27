module

public import Certificates.Data.Kernel.B433Alt.Struct

public section

namespace CFSG.KC.B4A

open CFSG.KC.Y333

section
variable (LP : Nat → Nat)

@[expose] noncomputable def evL : List Nat → Nat → Nat
  | a :: b :: t, x => pget (LP (Nat.add 10 (Nat.add (Nat.mul 10 a) b))) (evL t x)
  | [a], x => pget (LP a) x
  | [], x => x

@[expose] noncomputable def evR : List Nat → Nat → Nat
  | a :: b :: t, x => evR t (pget (LP (Nat.add 10 (Nat.add (Nat.mul 10 b) a))) x)
  | [a], x => pget (LP a) x
  | [], x => x

variable (W : Nat → List Nat)

@[expose] noncomputable def evT : List Nat → Nat → Nat
  | [], x => x
  | r :: rs, x => Bool.rec (motive := fun _ => Nat) (evL LP (W (Nat.div r 2)) (evT rs x))
      (evR LP (W (Nat.div r 2)) (evT rs x)) (Nat.beq (Nat.mod r 2) 1)

@[expose] noncomputable def evTI : List Nat → Nat → Nat
  | [], x => x
  | r :: rs, x => evTI rs (Bool.rec (motive := fun _ => Nat) (evR LP (W (Nat.div r 2)) x)
      (evL LP (W (Nat.div r 2)) x) (Nat.beq (Nat.mod r 2) 1))

end

@[expose] noncomputable def iter (f : Nat → Nat) : Nat → Nat → Nat
  | 0, x => x
  | n + 1, x => f (iter f n x)

@[expose] noncomputable def belowAll (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i acc => andB acc (f i)) n

@[expose] noncomputable def bp5 (i : Nat) : Nat := fld BASE5 (Nat.mul 16 i) 65535

@[expose] noncomputable def fix5 (f : Nat → Nat) : Bool :=
  belowAll 5 fun i => Nat.beq (f (bp5 i)) (bp5 i)

@[expose] noncomputable def lettersOK (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun c _ acc => andB (Nat.blt c 10) acc) l

@[expose] noncomputable def nodupB (l : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun p _ ih used => andB (notB (Nat.beq (Nat.land (Nat.shiftRight used p) 1) 1))
      (ih (Nat.lor used (Nat.shiftLeft 1 p)))) l

@[expose] noncomputable def orbListChk (ev : List Nat → Nat → Nat) (gens : List (List Nat)) (b : Nat)
    (P Q I : List Nat) : Bool :=
  andB (Nat.beq (P.getD 0 0) b) (andB (Nat.blt 0 P.length) (andB (nodupB P 0)
    (belowAll P.length fun i => Bool.rec (motive := fun _ => Bool)
      (andB (Nat.blt (Q.getD i 0) i)
        (Nat.beq (ev (gens.getD (I.getD i 0) []) (P.getD (Q.getD i 0) 0)) (P.getD i 0)))
      true (Nat.beq i 0))))

end CFSG.KC.B4A

end
