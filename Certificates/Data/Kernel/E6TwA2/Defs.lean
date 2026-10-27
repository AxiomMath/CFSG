module

public section

namespace Certificates.E6TwA2K

@[expose] noncomputable def andB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) false b a

@[expose] noncomputable def orB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) b true a

@[expose] noncomputable def notB (b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) true false b

@[expose] noncomputable def bitB (x n : Nat) : Bool :=
  Nat.blt (nat_lit 0) (Nat.land x (Nat.shiftLeft (nat_lit 1) n))

@[expose] noncomputable def letN {α : Type} (y : Nat) (k : Nat → α) : α :=
  Nat.rec (motive := fun _ => α) (k (nat_lit 0)) (fun m _ => k (Nat.succ m)) y

@[expose] noncomputable def forceN {α : Type} (y : Nat) (k : Nat → α) : α :=
  Bool.rec (motive := fun _ => α) (k y) (k y) (Nat.beq y (nat_lit 0))

@[expose] noncomputable def hd (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun x _ _ => x) l

@[expose] noncomputable def tl (l : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun _ t _ => t) l

@[expose] noncomputable def codesOf (r : List Nat) : List Nat := tl (tl (tl (tl (tl r))))

@[expose] noncomputable def allL (l : List Nat) (f : Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => andB (f x) ih) l

@[expose] noncomputable def anyL (l : List Nat) (f : Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun x _ ih => orB (f x) ih) l

@[expose] noncomputable def lenL (l : List (List Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) l

@[expose] noncomputable def fld (x w i : Nat) : Nat :=
  Nat.land (Nat.shiftRight x (Nat.mul w i)) (Nat.sub (Nat.shiftLeft (nat_lit 1) w) (nat_lit 1))

@[expose] noncomputable def d3 (n p : Nat) : Nat := Nat.mod (Nat.div n p) (nat_lit 3)

@[expose] noncomputable def rr (c s : Nat) : Nat :=
  Nat.mod (Nat.add (Nat.land (Nat.shiftRight c s) (nat_lit 15)) (nat_lit 1)) (nat_lit 3)

@[expose] noncomputable def pk (a0 a1 a2 a3 a4 a5 : Nat) : Nat :=
  Nat.lor a0 (Nat.lor (Nat.shiftLeft a1 2) (Nat.lor (Nat.shiftLeft a2 4)
    (Nat.lor (Nat.shiftLeft a3 6) (Nat.lor (Nat.shiftLeft a4 8) (Nat.shiftLeft a5 10)))))

@[expose] noncomputable def kd (v j : Nat) : Nat := Nat.land (Nat.shiftRight v j) (nat_lit 3)

@[expose] noncomputable def kvR (c : Nat) : Nat :=
  pk (rr c 0) (rr c 4) (rr c 8) (rr c 12) (rr c 16) (rr c 20)

@[expose] noncomputable def dd (a b : Nat) : Nat :=
  Nat.mod (Nat.add a (Nat.mul (nat_lit 2) b)) (nat_lit 3)

@[expose] noncomputable def kvD (c1 c2 : Nat) : Nat :=
  pk (dd (rr c1 0) (rr c2 0)) (dd (rr c1 4) (rr c2 4)) (dd (rr c1 8) (rr c2 8))
    (dd (rr c1 12) (rr c2 12)) (dd (rr c1 16) (rr c2 16)) (dd (rr c1 20) (rr c2 20))

@[expose] noncomputable def kvT (n : Nat) : Nat :=
  pk (d3 n 1) (d3 n 3) (d3 n 9) (d3 n 27) (d3 n 81) (d3 n 243)

@[expose] noncomputable def pr (c v : Nat) : Nat :=
  Nat.mod (Nat.add (Nat.mul (d3 c 1) (kd v 0)) (Nat.add (Nat.mul (d3 c 3) (kd v 2))
    (Nat.add (Nat.mul (d3 c 9) (kd v 4)) (Nat.add (Nat.mul (d3 c 27) (kd v 6))
      (Nat.add (Nat.mul (d3 c 81) (kd v 8)) (Nat.mul (d3 c 243) (kd v 10))))))) (nat_lit 3)

@[expose] noncomputable def formF (v c : Nat) : Nat :=
  Nat.add (Nat.mul (kd v 0) (Nat.add (rr c 0) (rr c 8)))
  (Nat.add (Nat.mul (kd v 2) (Nat.add (rr c 4) (rr c 12)))
  (Nat.add (Nat.mul (kd v 4) (Nat.add (rr c 8) (Nat.add (rr c 0) (rr c 12))))
  (Nat.add (Nat.mul (kd v 6) (Nat.add (rr c 12) (Nat.add (rr c 4) (Nat.add (rr c 8) (rr c 16)))))
  (Nat.add (Nat.mul (kd v 8) (Nat.add (rr c 16) (Nat.add (rr c 12) (rr c 20))))
    (Nat.mul (kd v 10) (Nat.add (rr c 20) (rr c 16)))))))

@[expose] noncomputable def inR (c lo : Nat) : Bool :=
  andB (Nat.ble lo c) (Nat.blt c (Nat.mul (nat_lit 2) lo))

@[expose] noncomputable def normB (c : Nat) : Bool :=
  orB (Nat.beq c 0) (orB (inR c 1) (orB (inR c 3) (orB (inR c 9) (orB (inR c 27)
    (orB (inR c 81) (inR c 243))))))

@[expose] noncomputable def posOf (c : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (Nat.sub c 121)
    (Bool.rec (motive := fun _ => Nat) (Nat.sub c 40)
      (Bool.rec (motive := fun _ => Nat) (Nat.sub c 13)
        (Bool.rec (motive := fun _ => Nat) (Nat.sub c 4)
          (Bool.rec (motive := fun _ => Nat) (Nat.sub c 1) c (Nat.blt c 3))
          (Nat.blt c 9)) (Nat.blt c 27)) (Nat.blt c 81)) (Nat.blt c 243)

@[expose] noncomputable def codesOK (cs : List Nat) (v1 v2 : Nat) : Bool :=
  allL cs fun c => andB (normB c) (andB (Nat.beq (pr c v1) 0) (Nat.beq (pr c v2) 0))

@[expose] noncomputable def hexEq (c1 c2 c3 s : Nat) : Bool :=
  Nat.beq (Nat.add (Nat.land (Nat.shiftRight c1 s) 15) (Nat.land (Nat.shiftRight c2 s) 15))
    (Nat.add (Nat.land (Nat.shiftRight c3 s) 15) 8)

@[expose] noncomputable def sumOK (c1 c2 c3 : Nat) : Bool :=
  andB (hexEq c1 c2 c3 0) (andB (hexEq c1 c2 c3 4) (andB (hexEq c1 c2 c3 8)
    (andB (hexEq c1 c2 c3 12) (andB (hexEq c1 c2 c3 16) (hexEq c1 c2 c3 20)))))

@[expose] noncomputable def recOK (R : Nat) (r : List Nat) : Bool :=
  letN (hd r) fun k => letN (hd (tl r)) fun i1 => letN (hd (tl (tl r))) fun i2 =>
  letN (hd (tl (tl (tl r)))) fun i3 => letN (hd (tl (tl (tl (tl r))))) fun di =>
  letN (fld R 24 i1) fun c1 => letN (fld R 24 i2) fun c2 => letN (fld R 24 i3) fun c3 =>
  Bool.rec (motive := fun _ => Bool)
    (andB (Nat.beq k 1) (andB (Nat.blt i1 72) (andB (Nat.blt i2 72) (andB (Nat.blt i3 72)
      (andB (Nat.blt di 729) (andB (sumOK c1 c2 c3)
        (letN (kvT di) fun v2 =>
          andB (Nat.blt 0 (Nat.mod (formF v2 c3) 3))
            (letN (kvD c1 c2) fun v1 => codesOK (codesOf r) v1 v2))))))))
    (andB (Nat.blt i1 72) (letN (kvR c1) fun v1 => codesOK (codesOf r) v1 0))
    (Nat.beq k 0)

@[expose] noncomputable def recsOK (R : Nat) (ws : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun r _ ih => andB (recOK R r) ih) ws

@[expose] noncomputable def plOf (cs : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun c _ ih => Nat.lor (Nat.shiftLeft (nat_lit 1) (posOf c)) ih) cs

@[expose] noncomputable def rkOf (PL : Nat) (cs : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun c _ ih => Nat.lor (Nat.shiftLeft PL (Nat.mul (nat_lit 365) (posOf c))) ih) cs

@[expose] noncomputable def repOK (p : Nat) (ws : List (List Nat)) : Bool :=
  forceN (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 133225)) (nat_lit 1)) fun F =>
    Nat.beq F (List.rec (motive := fun _ => Nat) 0
      (fun r _ ih => letN (plOf (codesOf r)) fun PL =>
        Bool.rec (motive := fun _ => Nat) ih (Nat.lor (rkOf PL (codesOf r)) ih) (bitB PL p)) ws)

@[expose] noncomputable def cIA : Nat := 52487049861

@[expose] noncomputable def cb (i j : Nat) : Nat :=
  Nat.land (Nat.shiftRight cIA (Nat.add (Nat.mul 6 i) j)) 1

@[expose] noncomputable def actK (n i : Nat) : Nat :=
  letN (d3 n (Nat.pow 3 i)) fun di =>
    Nat.add (Nat.mod (Nat.add (d3 n 1) (Nat.mul di (cb i 0))) 3)
    (Nat.add (Nat.mul 3 (Nat.mod (Nat.add (d3 n 3) (Nat.mul di (cb i 1))) 3))
    (Nat.add (Nat.mul 9 (Nat.mod (Nat.add (d3 n 9) (Nat.mul di (cb i 2))) 3))
    (Nat.add (Nat.mul 27 (Nat.mod (Nat.add (d3 n 27) (Nat.mul di (cb i 3))) 3))
    (Nat.add (Nat.mul 81 (Nat.mod (Nat.add (d3 n 81) (Nat.mul di (cb i 4))) 3))
      (Nat.mul 243 (Nat.mod (Nat.add (d3 n 243) (Nat.mul di (cb i 5))) 3))))))

@[expose] noncomputable def applyW (w : List Nat) (n : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun n => n) (fun i _ ih n => letN (actK n i) ih) w n

@[expose] noncomputable def wordsOK (rs : List Nat) (ws : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun w _ ih n => letN n fun n =>
      andB (letN (applyW w n) fun m => anyL rs fun r => Nat.beq m r) (ih (Nat.succ n))) ws 0

@[expose] noncomputable def negK (n : Nat) : Nat :=
  Nat.add (Nat.mod (Nat.mul 2 (d3 n 1)) 3) (Nat.add (Nat.mul 3 (Nat.mod (Nat.mul 2 (d3 n 3)) 3))
    (Nat.add (Nat.mul 9 (Nat.mod (Nat.mul 2 (d3 n 9)) 3))
    (Nat.add (Nat.mul 27 (Nat.mod (Nat.mul 2 (d3 n 27)) 3))
    (Nat.add (Nat.mul 81 (Nat.mod (Nat.mul 2 (d3 n 81)) 3))
      (Nat.mul 243 (Nat.mod (Nat.mul 2 (d3 n 243)) 3))))))

@[expose] noncomputable def normC (n : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (negK n) n (normB n)

@[expose] noncomputable def digM (a n m p : Nat) : Bool :=
  Nat.beq (d3 n p) (Nat.mod (Nat.mul a (d3 m p)) 3)

@[expose] noncomputable def digsM (a n m : Nat) : Bool :=
  andB (digM a n m 1) (andB (digM a n m 3) (andB (digM a n m 9) (andB (digM a n m 27)
    (andB (digM a n m 81) (digM a n m 243)))))

@[expose] noncomputable def normOK (N : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun n ih => andB (letN (normC n) fun m =>
      andB (normB m) (orB (digsM 1 n m) (digsM 2 n m))) ih) N

@[expose] noncomputable def rootsOK (R : Nat) (C : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun k => Nat.beq k (nat_lit 72))
    (fun c _ ih k => andB (Nat.beq (fld R 24 k) c) (ih (Nat.succ k))) C (nat_lit 0)

end Certificates.E6TwA2K

end
