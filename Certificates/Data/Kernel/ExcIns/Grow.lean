module

public import Certificates.Data.Kernel.ExcExt.TabCheck

public section

namespace CFSG.ExcInsK

open CFSG.ExcExtK

@[expose] noncomputable def rowK (K : KT) (u : Nat) : Nat :=
  Nat.land (Nat.shiftRight K.rt (Nat.mul 7 (Nat.mul K.r u))) (Nat.sub (Nat.shiftLeft 1 (Nat.mul 7 K.r)) 1)

@[expose] noncomputable def imgK (row r c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun t acc => nif (bit c t) (Nat.lor acc (Nat.shiftLeft 1 (ln7 row t))) acc) r

@[expose] noncomputable def wordK (K : KT) (w : List Nat) (c : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) c (fun u _ acc => imgK (rowK K u) K.r acc) w

@[expose] noncomputable def gensW (gm : Nat) (w : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun u _ acc => band (bit gm u) acc) w

@[expose] noncomputable def digP (W k a : Nat) : Nat :=
  Nat.mul (Nat.shiftLeft (Nat.sub (Nat.shiftLeft 1 (Nat.pow 3 k)) 1) (Nat.mul a (Nat.pow 3 k)))
    (Nat.div (Nat.sub (Nat.shiftLeft 1 W) 1) (Nat.sub (Nat.shiftLeft 1 (Nat.mul 3 (Nat.pow 3 k))) 1))

@[expose] noncomputable def termP (W k f t : Nat) : Nat :=
  Nat.lor (nif (Nat.beq (Nat.mod t 3) 0) (digP W k 0) 0)
    (Nat.lor (nif (Nat.beq (Nat.mod f 3) (Nat.mod t 3)) (digP W k 1) 0)
      (nif (Nat.beq (Nat.mod (Nat.mul 2 f) 3) (Nat.mod t 3)) (digP W k 2) 0))

@[expose] noncomputable def addP (W Z O T E0 E1 E2 : Nat) : Nat :=
  Nat.lor (Nat.lor (Nat.lor (Nat.land Z E0) (Nat.land O E2)) (Nat.land T E1))
    (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.lor (Nat.land Z E1) (Nat.land O E0)) (Nat.land T E2)) W)
      (Nat.shiftLeft (Nat.lor (Nat.lor (Nat.land Z E2) (Nat.land O E1)) (Nat.land T E0)) (Nat.mul 2 W)))

@[expose] noncomputable def stepP (W k f st : Nat) : Nat :=
  addP W (Nat.land st (Nat.sub (Nat.shiftLeft 1 W) 1))
    (Nat.land (Nat.shiftRight st W) (Nat.sub (Nat.shiftLeft 1 W) 1)) (Nat.shiftRight st (Nat.mul 2 W))
    (termP W k f 0) (termP W k f 1) (termP W k f 2)

@[expose] noncomputable def planeK (K : KT) (W s : Nat) : Nat :=
  Nat.land (Nat.rec (motive := fun _ => Nat) (Nat.sub (Nat.shiftLeft 1 W) 1)
    (fun k st => stepP W k (fK K s k) st) K.d) (Nat.sub (Nat.shiftLeft 1 W) 1)

@[expose] noncomputable def planesFrom (K : KT) (W : Nat) (PL : List Nat) (s : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun s => Nat.beq s K.r)
    (fun p _ ih s => band (Nat.beq p (planeK K W s)) (ih (Nat.succ s))) PL s

@[expose] noncomputable def planesOK (K : KT) (W : Nat) (PL : List Nat) : Bool := planesFrom K W PL 0

@[expose] noncomputable def meetK (PL : List Nat) (c s A : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ A => A)
    (fun p _ ih s A => ih (Nat.succ s) (nif (bit c s) (Nat.land A p) A)) PL s A

@[expose] noncomputable def overK (PL : List Nat) (A s acc : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun p _ ih s acc => ih (Nat.succ s)
      (nif (Nat.beq (Nat.land A p) A) (Nat.lor acc (Nat.shiftLeft 1 s)) acc)) PL s acc

@[expose] noncomputable def closK (PL : List Nat) (W c : Nat) : Nat :=
  overK PL (meetK PL c 0 (Nat.sub (Nat.shiftLeft 1 W) 1)) 0 0

@[expose] noncomputable def stepK (K : KT) (M S : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) S
    (fun t acc => nif (bit S t) (Nat.lor acc (Nat.land (adjK K t) M)) acc) K.r

@[expose] noncomputable def nextK (ih : Nat → Nat) (S S' : Nat) : Nat := nif (Nat.beq S' S) S (ih S')

@[expose] noncomputable def growIt (K : KT) (M n S : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun _ ih S => nextK ih S (stepK K M S)) n S

@[expose] noncomputable def growCK (K : KT) (PL : List Nat) (W c : Nat) : Nat :=
  growIt K (closK PL W c) K.r c

@[expose] noncomputable def recK (K : KT) (PL : List Nat) (W gm R nr : Nat) (skip : Bool) (c j : Nat)
    (yw : Nat × List Nat) : Bool :=
  bor (band skip (bor (bit c j) (Nat.beq (Nat.land (adjK K j) c) 0)))
    (Prod.rec (motive := fun _ => Bool) (fun y w =>
      band (Nat.blt y nr) <| band (gensW gm w) <|
        band (Nat.blt (Nat.lor c (Nat.shiftLeft 1 j)) (Nat.shiftLeft 1 K.r))
          (Nat.beq (growCK K PL W (Nat.lor c (Nat.shiftLeft 1 j))) (wordK K w (ln128 R y)))) yw)

@[expose] noncomputable def recsFrom (K : KT) (PL : List Nat) (W gm R nr : Nat) (skip : Bool) (c : Nat)
    (L : List (Nat × List Nat)) (j : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun j => Nat.beq j K.r)
    (fun yw _ ih j => band (recK K PL W gm R nr skip c j yw) (ih (Nat.succ j))) L j

@[expose] noncomputable def repsOK (R nr r : Nat) : Bool :=
  allN nr fun x => Nat.blt (ln128 R x) (Nat.shiftLeft 1 r)

@[expose] noncomputable def recsK (K : KT) (PL : List Nat) (W gm R nr : Nat) (skip : Bool) (c : Nat)
    (L : List (Nat × List Nat)) : Bool :=
  recsFrom K PL W gm R nr skip c L 0

end CFSG.ExcInsK

end
