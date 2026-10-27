module

public import Certificates.Data.Kernel.Misc.G24

public section

namespace CFSG.KC.Misc.G23

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc CFSG.KC.Misc.G24

@[expose] noncomputable def wsK (c : Nat) : Bool :=
  orB (Nat.beq c 32) (orB (Nat.beq c 9) (orB (Nat.beq c 10) (orB (Nat.beq c 13)
    (orB (Nat.beq c 11) (Nat.beq c 12)))))

@[expose] noncomputable def afterNL (cs : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil
    (fun c t ih => Bool.rec (motive := fun _ => List Nat) ih t (Nat.beq c 10)) cs

@[expose] noncomputable def entryK (c : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) 0 (Nat.sub c 48) (andB (Nat.ble 48 c) (Nat.ble c 57))

@[expose] noncomputable def blowBits (i e : Nat) : Nat :=
  letN (Nat.div i 27) fun r => letN (Nat.mod i 27) fun c =>
  letN (Nat.land e 1) fun x₀ => letN (Nat.land (Nat.shiftRight e 1) 1) fun x₁ =>
  letN (Nat.add (Nat.mul 108 r) (Nat.mul 2 c)) fun p =>
  Nat.lor (Nat.lor (Nat.shiftLeft x₀ p) (Nat.shiftLeft x₁ (Nat.succ p)))
    (Nat.lor (Nat.shiftLeft x₁ (Nat.add p 54)) (Nat.shiftLeft (Nat.xor x₀ x₁) (Nat.add p 55)))

@[expose] noncomputable def decodeK (cs : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun c _ ih i acc => Bool.rec (motive := fun _ => Nat)
      (ih (Nat.succ i) (Bool.rec (motive := fun _ => Nat) acc
        (Nat.lor acc (blowBits i (Nat.mod (entryK c) 4))) (Nat.blt i 729)))
      (ih i acc) (wsK c)) (afterNL cs) 0 0

@[expose] noncomputable def letterM (A B Bi l : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) Bi B (Nat.beq l 3))
    A (Nat.blt l 2)

@[expose] noncomputable def wordM (A B Bi : Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (oneF2 54) (fun l _ ih => mulF2 54 (letterM A B Bi l) ih) w

@[expose] noncomputable def commsW (ps : List (List Nat × List Nat)) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil
    (fun p _ ih => appN (Prod.rec (motive := fun _ => List Nat) (fun u v => commK u v) p) ih) ps

@[expose] noncomputable def coverW (R : List (List Nat)) (P : List (List (List Nat × List Nat))) :
    List (List Nat) :=
  appLL (appLL
    (List.rec (motive := fun _ => List (List Nat)) List.nil (fun r _ ih => List.cons (commK [1] r) ih) R)
    (List.rec (motive := fun _ => List (List Nat)) List.nil (fun r _ ih => List.cons (commK [3] r) ih) R))
    [List.cons 0 (commsW (nthP P 0)), List.cons 2 (commsW (nthP P 1))]
where
  appLL (a b : List (List Nat)) : List (List Nat) :=
    List.rec (motive := fun _ => List (List Nat)) b (fun x _ ih => List.cons x ih) a

@[expose] noncomputable def g23K (cA cB : List Nat) (Ab Bb : Nat) (R : List (List Nat))
    (P : List (List (List Nat × List Nat))) (six : List Nat) : Bool :=
  andB (Nat.beq (decodeK cA) Ab) <| andB (Nat.beq (decodeK cB) Bb) <|
  letB (mulF2 54 Bb Bb) fun Bi =>
  andB (Nat.beq (mulF2 54 Ab Ab) (oneF2 54)) <| andB (Nat.beq (mulF2 54 Bb Bi) (oneF2 54)) <|
  andB (allLL (coverW R P) fun w => Nat.beq (wordM Ab Bb Bi w) (oneF2 54)) <|
    letB (wordM Ab Bb Bi six) fun Z => andB (Nat.beq (mulF2 54 Z (mulF2 54 Z Z)) (oneF2 54))
      (Nat.beq (bit Z 1) 1)

end CFSG.KC.Misc.G23

end
