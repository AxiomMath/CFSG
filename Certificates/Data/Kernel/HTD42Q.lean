module

public import Certificates.Data.Kernel.D4PlaneP

public section

namespace CFSG.KC.HTD42Q

open CFSG.KC.D4PlaneP

@[expose] noncomputable def frK (X : Nat) : Nat :=
  (X &&& m64) ||| (((X >>> 128) &&& m64) <<< 64) |||
    ((((X >>> 64) ^^^ (X >>> 128)) &&& m64) <<< 128)

@[expose] noncomputable def frN (n X : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) X (fun _ Y => frK Y) n

@[expose] noncomputable def mulQ (p q : Nat × Nat) : Nat × Nat :=
  (mulP p.1 (frN p.2 q.1), Nat.mod (Nat.add p.2 q.2) 3)

@[expose] noncomputable def symQ (ls : List Nat) (s : Nat) : Nat × Nat :=
  Bool.rec (motive := fun _ => Nat × Nat) (oneP, 1) (letP ls s, 0) (Nat.blt s 18)

@[expose] noncomputable def wordQ (ls : List Nat) (w : List Nat) : Nat × Nat :=
  List.rec (motive := fun _ => Nat × Nat) (oneP, 0) (fun s _ p => mulQ (symQ ls s) p) w

@[expose] noncomputable def eqQ (p q : Nat × Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Nat.beq p.2 q.2) (Nat.beq p.1 q.1)

@[expose] noncomputable def fixQ (y : Nat × Nat) (F : Nat) : Bool :=
  Nat.beq (mulP y.1 (frN y.2 F)) (mulP F y.1)

@[expose] noncomputable def cubeQ (y : Nat × Nat) : Bool := eqQ (mulQ y (mulQ y y)) (oneP, 0)

@[expose] noncomputable def witY (G : List (Nat × Nat)) (y : Nat × Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) true
    (List.rec (motive := fun _ => Bool) false
      (fun g _ r => Bool.rec (motive := fun _ => Bool) r true
        (Bool.rec (motive := fun _ => Bool) false (fixQ y g.2) (fixQ y g.1))) G)
    (cubeQ y)

@[expose] noncomputable def witAll (x : Nat × Nat) (G : List (Nat × Nat)) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun e _ r => Bool.rec (motive := fun _ => Bool) false r (witY G (mulQ (e, 0) x))) L

@[expose] noncomputable def planeQ (u v : Nat) : Bool :=
  Bool.and' (cube1P u) <| Bool.and' (cube1P v) <| Bool.and' (commP u v) <|
    Bool.and' (Bool.not' (Nat.beq u oneP)) <| Bool.and' (Bool.not' (Nat.beq v oneP)) <|
      Bool.and' (Bool.not' (Nat.beq v u)) (Bool.not' (Nat.beq v (mulP u u)))

@[expose] noncomputable def planesQ (G : List (Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun g _ r => Bool.rec (motive := fun _ => Bool) false r (planeQ g.1 g.2)) G

@[expose] def gensI : List (Nat × Nat) :=
  [(1, 52), (2, 51), (4, 43), (5, 47), (13, 24), (15, 27), (17, 18), (19, 26), (20, 29), (32, 33)]

@[expose] noncomputable def gensP (es : List Nat) : List (Nat × Nat) :=
  List.rec (motive := fun _ => List (Nat × Nat)) []
    (fun p _ r => (atP es p.1, atP es p.2) :: r) gensI

@[expose] def xW : List Nat := [18, 18, 16, 12, 17, 7, 16, 10, 17, 7, 11, 17]

end CFSG.KC.HTD42Q

end
