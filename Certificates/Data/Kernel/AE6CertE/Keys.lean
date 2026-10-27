module

public import Certificates.Data.Kernel.Spor.Chain

public section

namespace Certificates.AE6CertEK

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def wlkK (ws : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun p => p)
    (fun X _ ih p => ih (pg (nat_lit 9) (mask (nat_lit 9)) X p)) ws

@[expose] noncomputable def keyK (O ws : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun o _ ih => Nat.add (Nat.shiftLeft (nat_lit 1) (wlkK ws o)) ih) O

@[expose] noncomputable def getK (T : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun X _ ih c => Nat.rec (motive := fun _ => Nat) X (fun c' _ => ih c') c) T

@[expose] noncomputable def convK (T w : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun c _ ih => getK T c :: ih) w

@[expose] noncomputable def notInK (a : Nat) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun b _ ih => bAnd(Bool.not (Nat.beq a b), ih)) L

@[expose] noncomputable def nodupK (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a t ih => bAnd(notInK a t, ih)) L

@[expose] noncomputable def memK (x : Nat) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun b _ ih => Bool.rec (motive := fun _ => Bool) ih true (Nat.beq x b)) L

@[expose] noncomputable def invarK (X : Nat) (O : List Nat) (n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun x ih => bAnd(Bool.beq (memK (pg (nat_lit 9) (mask (nat_lit 9)) X x) O) (memK x O), ih)) n

@[expose] noncomputable def invoK (X : Nat) (n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun x ih => bAnd(Nat.beq (pg (nat_lit 9) (mask (nat_lit 9)) X
      (pg (nat_lit 9) (mask (nat_lit 9)) X x)) x, ih)) n

@[expose] noncomputable def mvK (w : List Nat) (d : Nat) : List Nat :=
  Bool.rec (motive := fun _ => List Nat)
    (Bool.rec (motive := fun _ => List Nat) [] w (Nat.beq d (nat_lit 4)))
    [Nat.add d d] (Nat.blt d (nat_lit 4))

@[expose] noncomputable def expK (w : List Nat) (f : Nat) : Nat → List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun _ ih x => Nat.rec (motive := fun _ => List Nat) []
      (fun d _ => List.append (mvK w d) (ih (Nat.shiftRight x (nat_lit 3))))
      (Nat.land x (nat_lit 7))) f

@[expose] noncomputable def laneK (V t : Nat) : Nat :=
  Nat.land (Nat.shiftRight V (Nat.mul (nat_lit 64) t)) (nat_lit 18446744073709551615)

@[expose] noncomputable def pathK (T O w : List Nat) (V : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun t ih => bAnd(bIf(memK (Nat.add (Nat.add t t) (nat_lit 1)) w,
      Nat.beq (keyK O (convK T (expK w (nat_lit 21) (laneK V t))))
        (keyK O (convK T [Nat.add (Nat.add t t) (nat_lit 1)])), true), ih)) (nat_lit 4)

@[expose] noncomputable def pathsK (T O : List Nat) (W : Nat → List Nat) (F : Nat → Nat)
    (lo n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun s ih => bAnd(pathK T O (W (Nat.add lo s)) (F (Nat.add lo s)), ih)) n

@[expose] noncomputable def keysK (T O : List Nat) (W : Nat → List Nat) (n : Nat) : Bool :=
  nodupK ((List.range n).map fun j => keyK O (convK T (W j)))

@[expose] def eO0 : List Nat :=
  [24, 25, 26, 27, 28, 29, 30, 31, 88, 89, 90, 91, 92, 93, 94, 95]

@[expose] def eO1 : List Nat :=
  [144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215]

@[expose] def eO2 : List Nat :=
  [264, 265, 266, 267, 268, 269, 270, 271, 328, 329, 330, 331, 332, 333, 334, 335]

end Certificates.AE6CertEK

end
