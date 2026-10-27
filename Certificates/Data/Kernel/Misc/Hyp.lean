module

public import Certificates.Data.Kernel.Misc.Xi

public section

namespace CFSG.KC.Misc.Hyp

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc CFSG.KC.Misc.O73 CFSG.KC.Misc.T46
  CFSG.KC.Misc.Polar CFSG.KC.Misc.Lines CFSG.KC.Misc.Xi

@[expose] noncomputable def membersK (S : Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) [] (fun p acc => Bool.rec (motive := fun _ => List Nat) acc
    (List.cons p acc) (bitK S p)) 693

@[expose] noncomputable def clStepK (TP : Nat → Nat) (F : Nat) : Nat :=
  letB' (membersK F) fun M =>
    List.rec (motive := fun _ => Nat) F (fun u _ ih => letN (TP u) fun T =>
      List.rec (motive := fun _ => Nat) ih (fun v _ ih2 => Nat.lor ih2 (Nat.shiftLeft 1 (at' 10 T v)))
        M) M
where
  letB' (l : List Nat) (k : List Nat → Nat) : Nat :=
    List.rec (motive := fun _ => List Nat → Nat) (fun acc => k acc.reverse)
      (fun x _ ih acc => letN x fun x => ih (List.cons x acc)) l []

@[expose] noncomputable def startK (UP PP : Nat) (sel : List Nat) (j : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 1 (fun i acc => letN (wordM7.nthN sel i) fun s =>
    letN (line3 UP PP 0 s) fun t => letN (Nat.mod (Nat.div j (Nat.pow 4 i)) 4) fun d =>
    Nat.lor acc (Nat.shiftLeft 1 (Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat)
        (Bool.rec (motive := fun _ => Nat) (Nat.div t 1048576) (Nat.mod (Nat.div t 1024) 1024)
          (Nat.beq d 2))
        (Nat.mod t 1024) (Nat.beq d 1)) s (Nat.beq d 0)))) 5

@[expose] noncomputable def lamK (UP PP : Nat) (TP LB : Nat → Nat) (sel : List Nat) (lo n : Nat) :
    Bool :=
  allN n fun d => letB (Nat.add lo d) fun j => impB (Nat.blt j 1024) <|
    Nat.beq (LB j) (clStepK TP (clStepK TP (clStepK TP (startK UP PP sel j))))

@[expose] noncomputable def liAt (LI : Nat → Nat) (p : Nat) : Nat :=
  at' 1024 (LI (Nat.div p 64)) (Nat.mod p 64)

@[expose] noncomputable def liK (LB LI : Nat → Nat) (lo n : Nat) : Bool :=
  allN n fun d => letB (Nat.add lo d) fun j => impB (Nat.blt j 1024) <| letB (LB j) fun L =>
    andB (Nat.blt L (Nat.shiftLeft 1 693)) <|
    allN 693 fun p => Bool.rec (motive := fun _ => Bool) (notB (bitK L p)) (bitK L p)
      (bitK (liAt LI p) j)

@[expose] noncomputable def lamOKK (UP PP : Nat) (PB LB : Nat → Nat) (PL : Nat → List Nat)
    (sel : List Nat) : Bool :=
  letB (PB 0) fun P0 =>
  andB (Nat.beq (lenN sel) 5) <|
  andB (allL sel fun s => andB (Nat.blt s 693) (andB (notB (Nat.beq s 0)) (bitK P0 s))) <|
  andB (allN 1024 fun j => letB (LB j) fun L => andB (bitK L 0)
    (Nat.beq (Nat.land L (Nat.xor P0 (Nat.sub (Nat.shiftLeft 1 693) 1))) 0)) <|
    allL (PL 0) fun y => impB (notB (Nat.beq y 0)) <|
      letB (Nat.sub (lineB UP PP 0 y) 1) fun Lb => allN 1024 fun j =>
        notB (Nat.beq (Nat.land Lb (LB j)) 0)

@[expose] noncomputable def wordsK (TP WT GI : Nat → Nat) (QB PW : Nat) : Bool :=
  andB (Nat.beq (Nat.rec (motive := fun _ => Nat) (Nat.add 1 (Nat.shiftLeft 1 693))
    (fun h acc => Nat.rec (motive := fun _ => Nat) acc (fun k acc2 => step h k acc2) 31) 693)
    (Nat.add (Nat.sub (Nat.shiftLeft 1 693) 1) (Nat.shiftLeft 693 693))) <|
  andB (Nat.beq (WT 0) (idP 693 10)) <|
    allN 693 fun x => letB (WT x) fun T => letB (GI x) fun G =>
      andB (Nat.beq (at' 10 T 0) x) <| andB (permK 693 10 G) <|
      andB (Nat.beq (compP 693 10 T G) (idP 693 10)) <|
        impB (notB (Nat.beq x 0)) <| letB (at' 20 PW x) fun e =>
          Nat.beq T (compP 693 10 (TP (Nat.div e 1024)) (WT (Nat.mod e 1024)))
where
  step (h k acc : Nat) : Nat :=
    letN acc fun acc => letN (Nat.land acc (Nat.sub (Nat.shiftLeft 1 693) 1)) fun seen =>
    letN (Nat.shiftRight acc 693) fun cnt => letN (at' 10 QB h) fun x =>
    letN (at' 10 (TP (Nat.mul 23 k)) x) fun y =>
    Bool.rec (motive := fun _ => Nat) 0
      (Bool.rec (motive := fun _ => Nat)
        (Bool.rec (motive := fun _ => Nat) 0
          (Nat.add (Nat.lor seen (Nat.shiftLeft 1 y)) (Nat.shiftLeft (Nat.succ cnt) 693))
          (andB (Nat.beq (at' 10 QB cnt) y)
            (Nat.beq (at' 20 PW y) (Nat.add x (Nat.mul 1024 (Nat.mul 23 k))))))
        acc (bitK seen y))
      (andB (notB (Nat.beq acc 0)) (Nat.blt h cnt))

@[expose] noncomputable def rootLK (UP PP : Nat) (HS : Nat → Nat) (PL : Nat → List Nat) (lo n : Nat) :
    Bool :=
  letB (HS 0) fun R1 => letB (HS 1408) fun R2 => letB (HS 2816) fun R3 =>
  allN n fun d => letB (Nat.add lo d) fun x => impB (Nat.blt x 693) <|
    allL (PL x) fun y => impB (Nat.blt x y) <| letB (line3 UP PP x y) fun t =>
      allL [R1, R2, R3] fun R => letB (cnt5 R x y t) fun c => orB (Nat.beq c 0) (Nat.beq c 2)
where
  cnt5 (R x y t : Nat) : Nat :=
    Nat.add (Nat.add (Nat.land (Nat.shiftRight R x) 1) (Nat.land (Nat.shiftRight R y) 1))
      (Nat.add (Nat.land (Nat.shiftRight R (Nat.mod t 1024)) 1)
        (Nat.add (Nat.land (Nat.shiftRight R (Nat.mod (Nat.div t 1024) 1024)) 1)
          (Nat.land (Nat.shiftRight R (Nat.div t 1048576)) 1)))

@[expose] noncomputable def rootCK (TP HS ML : Nat → Nat) : Bool :=
  allL [0, 1408, 2816] fun off => letB (HS off) fun R => letB (ML off) fun M =>
    allN 126 fun i => Nat.beq (imgP (TP (at' 10 M i)) M) R

@[expose] noncomputable def bitPosK (C : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun b pos => letN pos fun pos =>
    letN (Nat.add pos (Nat.pow 2 (Nat.sub 9 b))) fun q =>
      Bool.rec (motive := fun _ => Nat) pos q (notB (Nat.beq (Nat.shiftRight C q) 0))) 10

@[expose] noncomputable def nlK (GI : Nat → Nat) (PL NL : Nat → List Nat) (lo n : Nat) : Bool :=
  allN n fun d => letB (Nat.add lo d) fun x => impB (Nat.blt x 693) <| letB (GI x) fun G =>
    eqLN (NL x) (List.rec (motive := fun _ => List Nat) [] (fun y _ ih =>
      List.cons (Nat.add y (Nat.mul 1024 (at' 10 G y))) ih) (PL x))

@[expose] noncomputable def candK (LI : Nat → Nat) (NL : Nat → List Nat) (x I X : Nat) : Nat :=
  letN (Nat.lor I X) fun S => List.rec (motive := fun _ => Nat) (Nat.sub (Nat.shiftLeft 1 1024) 1)
    (fun e _ ih => Bool.rec (motive := fun _ => Nat) ih
      (letN (liAt LI (Nat.div e 1024)) fun Ly => Bool.rec (motive := fun _ => Nat)
        (Nat.land ih (Nat.xor Ly (Nat.sub (Nat.shiftLeft 1 1024) 1))) (Nat.land ih Ly)
        (bitK I (Nat.mod e 1024)))
      (bitK S (Nat.mod e 1024))) (NL x)

@[expose] noncomputable def extK (LB : Nat → Nat) (NL : Nat → List Nat) (x j S : Nat) : Nat :=
  letN (LB j) fun L => List.rec (motive := fun _ => Nat) S
    (fun e _ ih => Bool.rec (motive := fun _ => Nat)
      (Nat.lor ih (Nat.shiftLeft 1 (Nat.add 693 (Nat.mod e 1024))))
      (Nat.lor ih (Nat.shiftLeft 1 (Nat.mod e 1024)))
      (bitK L (Nat.div e 1024))) (NL x)

@[expose] noncomputable def passK (PB LB LI : Nat → Nat) (NL : Nat → List Nat) (I X : Nat) :
    Nat :=
  letN (Nat.xor (Nat.lor I X) (Nat.sub (Nat.shiftLeft 1 693) 1)) fun U0 =>
  Nat.rec (motive := fun _ => Nat) (Nat.lor I (Nat.shiftLeft X 693)) (fun x acc => letN acc fun acc =>
    Bool.rec (motive := fun _ => Nat) acc
      (letN (candK LI NL x I X) fun C =>
        Bool.rec (motive := fun _ => Nat)
          (Bool.rec (motive := fun _ => Nat) acc
            (Nat.lor (Nat.shiftLeft 1 1387) (extK LB NL x (bitPosK C) acc))
            (Nat.beq (Nat.land C (Nat.sub C 1)) 0))
          (Nat.lor acc (Nat.shiftLeft 1 1386)) (Nat.beq C 0))
      (andB (bitK I x) (notB (Nat.beq (Nat.land (PB x) U0) 0)))) 693

@[expose] noncomputable def pop1024 (C : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) C (fun i acc => letN acc fun acc =>
    letN (Nat.pow 2 i) fun w => letN (mask w) fun m =>
      Nat.add (Nat.land acc m) (Nat.land (Nat.shiftRight acc w) m)) 10
where
  mask (w : Nat) : Nat :=
    Nat.mul (Nat.div (Nat.sub (Nat.shiftLeft 1 1024) 1) (Nat.sub (Nat.shiftLeft 1 (Nat.mul 2 w)) 1))
      (Nat.sub (Nat.shiftLeft 1 w) 1)

@[expose] noncomputable def combK (a b : Nat) : Nat :=
  letN a fun a => letN b fun b => Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) 0 a (Nat.beq b 1)) b (Nat.beq a 1))
    0 (orB (Nat.beq a 0) (Nat.beq b 0))

end CFSG.KC.Misc.Hyp

end
