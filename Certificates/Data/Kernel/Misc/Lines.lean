module

public import Certificates.Data.Kernel.Misc.Polar

public section

namespace CFSG.KC.Misc.Lines

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc CFSG.KC.Misc.O73 CFSG.KC.Misc.T46 CFSG.KC.Misc.Polar

@[expose] noncomputable def bitK (S i : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight S i) 1) 1

@[expose] noncomputable def popK (S : Nat) : Nat :=
  letN S fun S => Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => Nat.add acc (Nat.land (Nat.shiftRight S i) 1)) 693

@[expose] noncomputable def isPt (c : Nat) : Bool :=
  andB (notB (Nat.beq c 0)) (andB (Nat.beq (hermR c c) 0) (Nat.beq (normK c) c))

@[expose] noncomputable def posK (UL : List Nat) (UP PP : Nat) : Bool :=
  andB (allL UL isPt) <| andB (Nat.blt PP (Nat.shiftLeft 1 (Nat.mul 10 4096))) <|
    allN 4096 fun c => letB (at' 10 PP c) fun j =>
      orB (andB (Nat.blt j 693) (Nat.beq (at' 12 UP j) c)) (andB (Nat.beq j 693) (notB (isPt c)))

@[expose] noncomputable def perpK (UP : Nat) (PB : Nat → Nat) (lo n : Nat) : Bool :=
  allN n fun d => letB (Nat.add lo d) fun x => impB (Nat.blt x 693) <|
    letB (PB x) fun Px => letB (at' 12 UP x) fun cx =>
      andB (Nat.blt Px (Nat.shiftLeft 1 693)) <|
        allN 693 fun y => Bool.rec (motive := fun _ => Bool)
          (notB (Nat.beq (hermR (at' 12 UP y) cx) 0)) (Nat.beq (hermR (at' 12 UP y) cx) 0)
          (bitK Px y)

@[expose] noncomputable def plK (PB : Nat → Nat) (PL : Nat → List Nat) : Bool :=
  allN 693 fun x => letLN' (PL x) fun l => andB (Nat.beq (lenN l) 181) <|
    andB (Nat.beq (List.rec (motive := fun _ => Nat) 0 (fun p _ ih => Nat.lor ih (Nat.shiftLeft 1 p)) l)
      (PB x)) <|
    List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
      (fun p _ ih prev => andB (Nat.blt prev (Nat.succ p)) (ih (Nat.succ p))) l 0
where
  letLN' (l : List Nat) (k : List Nat → Bool) : Bool :=
    List.rec (motive := fun _ => List Nat → Bool) (fun acc => k acc.reverse)
      (fun x _ ih acc => letB x fun x => ih (List.cons x acc)) l []

@[expose] noncomputable def line3 (UP PP x y : Nat) : Nat :=
  letN (at' 12 UP x) fun cx => letN (at' 12 UP y) fun cy =>
    Nat.add (at' 10 PP (normK (Nat.xor cx cy))) (Nat.mul 1024 (Nat.add
      (at' 10 PP (normK (Nat.xor cx (scaleK 2 cy))))
      (Nat.mul 1024 (at' 10 PP (normK (Nat.xor cx (scaleK 3 cy)))))))

@[expose] noncomputable def line5 (UP PP x y : Nat) : Bool :=
  letB (line3 UP PP x y) fun t => letB (Nat.mod t 1024) fun a =>
    letB (Nat.mod (Nat.div t 1024) 1024) fun b => letB (Nat.div t 1048576) fun c =>
      andB (andB (Nat.blt a 693) (andB (Nat.blt b 693) (Nat.blt c 693))) <|
      andB (notB (Nat.beq x y)) <|
      andB (andB (notB (Nat.beq a b)) (andB (notB (Nat.beq a c)) (notB (Nat.beq b c)))) <|
        allL [a, b, c] fun z => andB (notB (Nat.beq z x)) (notB (Nat.beq z y))

@[expose] noncomputable def lineB (UP PP x y : Nat) : Nat :=
  letN (line3 UP PP x y) fun t => Nat.lor (Nat.lor (Nat.shiftLeft 1 x) (Nat.shiftLeft 1 y))
    (Nat.lor (Nat.shiftLeft 1 (Nat.mod t 1024)) (Nat.lor (Nat.shiftLeft 1 (Nat.mod (Nat.div t 1024) 1024))
      (Nat.shiftLeft 1 (Nat.div t 1048576))))

@[expose] noncomputable def linesK (UP PP : Nat) (PB : Nat → Nat) (PL : Nat → List Nat) (lo n : Nat) :
    Bool :=
  allN n fun d => letB (Nat.add lo d) fun x => impB (Nat.blt x 693) <|
    allL (PL x) fun y => impB (Nat.blt x y) <| letB (PB y) fun Py =>
      letB (lineB UP PP x y) fun Lb => andB (line5 UP PP x y) <|
      andB (Nat.beq (lineB UP PP y x) Lb) <|
        Nat.beq (List.rec (motive := fun _ => Nat) (Nat.sub (Nat.shiftLeft 1 693) 1)
          (fun w _ ih => Bool.rec (motive := fun _ => Nat) ih (Nat.land ih (PB w)) (bitK Py w)) (PL x))
          Lb

@[expose] noncomputable def lineCnt (UP PP : Nat) (PL : Nat → List Nat) (lo n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun d acc => letN (Nat.add lo d) fun x =>
    Nat.add acc (List.rec (motive := fun _ => Nat) 0 (fun y _ ih => Nat.add ih
      (Bool.rec (motive := fun _ => Nat) 0
        (Bool.rec (motive := fun _ => Nat) 0 1 (Nat.beq (Nat.land (lineB UP PP x y)
          (Nat.sub (Nat.shiftLeft 1 y) 1)) (Nat.shiftLeft 1 x)))
        (andB (Nat.blt x 693) (Nat.blt x y)))) (PL x))) n

@[expose] noncomputable def twinsK (UP PP : Nat) (PB : Nat → Nat) (PL : Nat → List Nat) : Bool :=
  letB (Nat.sub (PB 0) 1) fun D => allL (PL 0) fun x => impB (notB (Nat.beq x 0)) <|
    letB (Nat.land (PB x) D) fun Ax => letB (lineB UP PP 0 x) fun Lb =>
      allL (PL 0) fun y => impB (andB (notB (Nat.beq y 0)) (notB (Nat.beq y x))) <|
        Bool.rec (motive := fun _ => Bool) (notB (bitK Lb y)) (bitK Lb y)
          (Nat.beq (Nat.land (PB y) D) Ax)

@[expose] noncomputable def tv0 (UP PP q : Nat) : Nat :=
  at' 10 PP (normK (tvK (at' 12 UP 0) (at' 12 UP q)))

@[expose] noncomputable def ppK (UP PP : Nat) (PB : Nat → Nat) (PL : Nat → List Nat) (lo n : Nat) :
    Bool :=
  letB (PB 0) fun P0 => allN n fun d => letB (Nat.add lo d) fun q =>
    impB (andB (Nat.blt q 693) (notB (bitK P0 q))) <| letB (Nat.land P0 (PB q)) fun Nb =>
    andB (Nat.beq (popK Nb) 45) <|
    andB (anyL (PL 0) fun a => andB (bitK Nb a) <| anyL (PL a) fun b =>
      andB (bitK Nb b) <| andB (notB (Nat.beq a b)) <|
        Nat.ble 3 (popK (Nat.land (lineB UP PP a b) Nb))) <|
    andB (allL (PL 0) fun a => impB (bitK Nb a) <| letB (Nat.land (PB a) Nb) fun Aa =>
      allL (PL a) fun b => impB (andB (bitK Nb b) (notB (Nat.beq a b)))
        (notB (Nat.beq (Nat.land (PB b) Nb) Aa))) <|
    letB (tv0 UP PP q) fun t => allN 693 fun q' => impB (notB (bitK P0 q')) <|
      impB (Nat.beq (Nat.land P0 (PB q')) Nb) (orB (Nat.beq q' q) (Nat.beq q' t))

end CFSG.KC.Misc.Lines

end
