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

@[expose] noncomputable def lnSel (b : Bool) (P : Nat) : Nat := Bool.rec (motive := fun _ => Nat) 0 P b

@[expose] noncomputable def lnCol (UP j : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun y acc => Nat.lor acc
    (lnSel (bitK UP (Nat.add (Nat.mul 12 y) j)) (Nat.shiftLeft 1 y))) 693

@[expose] noncomputable def mulLo (P0 P1 a : Nat) : Nat :=
  Nat.xor (lnSel (bitK a 0) P0) (lnSel (bitK a 1) P1)

@[expose] noncomputable def mulHi (P0 P1 a : Nat) : Nat :=
  Nat.xor (lnSel (bitK a 1) P0) (Nat.xor (lnSel (bitK a 0) P1) (lnSel (bitK a 1) P1))

@[expose] noncomputable def lnCj (c i : Nat) : Nat := f4K (crdK c i) (crdK c i)

@[expose] noncomputable def perpLH (C0 C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 c : Nat) : Nat :=
  letN (lnCj c 0) fun a0 => letN (lnCj c 1) fun a1 => letN (lnCj c 2) fun a2 =>
  letN (lnCj c 3) fun a3 => letN (lnCj c 4) fun a4 => letN (lnCj c 5) fun a5 =>
  Nat.lor
    (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor 0 (mulLo C0 C1 a0)) (mulLo C2 C3 a1))
      (mulLo C4 C5 a2)) (mulLo C6 C7 a3)) (mulLo C8 C9 a4)) (mulLo C10 C11 a5))
    (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor 0 (mulHi C0 C1 a0)) (mulHi C2 C3 a1))
      (mulHi C4 C5 a2)) (mulHi C6 C7 a3)) (mulHi C8 C9 a4)) (mulHi C10 C11 a5))

@[expose] noncomputable def perpK (UP : Nat) (PB : Nat → Nat) (lo n : Nat) : Bool :=
  letB (lnCol UP 0) fun C0 => letB (lnCol UP 1) fun C1 => letB (lnCol UP 2) fun C2 =>
  letB (lnCol UP 3) fun C3 => letB (lnCol UP 4) fun C4 => letB (lnCol UP 5) fun C5 =>
  letB (lnCol UP 6) fun C6 => letB (lnCol UP 7) fun C7 => letB (lnCol UP 8) fun C8 =>
  letB (lnCol UP 9) fun C9 => letB (lnCol UP 10) fun C10 => letB (lnCol UP 11) fun C11 =>
  allN n fun d => letB (Nat.add lo d) fun x => impB (Nat.blt x 693) <|
    letB (PB x) fun Px => letB (perpLH C0 C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 (at' 12 UP x)) fun LH =>
      andB (Nat.blt Px (Nat.shiftLeft 1 693)) <| andB (Nat.beq (Nat.land Px LH) 0)
        (Nat.beq (Nat.lor Px LH) (Nat.sub (Nat.shiftLeft 1 693) 1))

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

@[expose] noncomputable def lnS2 (c : Nat) : Nat :=
  letN (Nat.land c 1365) fun L => letN (Nat.land (Nat.shiftRight c 1) 1365) fun H =>
    Nat.lor H (Nat.shiftLeft (Nat.xor L H) 1)

@[expose] noncomputable def lnDig (c i r : Nat) : Nat :=
  letN (Nat.land (Nat.shiftRight c (Nat.mul 2 i)) 3) fun d =>
    Bool.rec (motive := fun _ => Nat) d r (Nat.beq d 0)

@[expose] noncomputable def lnLead (c : Nat) : Nat :=
  lnDig c 0 (lnDig c 1 (lnDig c 2 (lnDig c 3 (lnDig c 4 (lnDig c 5 0)))))

@[expose] noncomputable def lnNorm (c : Nat) : Nat :=
  letN (lnLead c) fun a => Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat) 0 c (Nat.beq a 1)) (lnS2 (lnS2 c)) (Nat.beq a 2))
    (lnS2 c) (Nat.beq a 3)

@[expose] noncomputable def lnTabK : Bool :=
  allN 4096 fun c => andB (Nat.beq (lnS2 c) (scaleK 2 c)) <|
    andB (Nat.beq (lnS2 (lnS2 c)) (scaleK 3 c)) (Nat.beq (lnNorm c) (normK c))

@[expose] noncomputable def line3 (UP PP x y : Nat) : Nat :=
  letN (at' 12 UP x) fun cx => letN (at' 12 UP y) fun cy => letN (lnS2 cy) fun c2 =>
    Nat.add (at' 10 PP (lnNorm (Nat.xor cx cy))) (Nat.mul 1024 (Nat.add
      (at' 10 PP (lnNorm (Nat.xor cx c2)))
      (Nat.mul 1024 (at' 10 PP (lnNorm (Nat.xor cx (lnS2 c2)))))))

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

@[expose] noncomputable def lnMin (a b : Nat) : Nat := Bool.rec (motive := fun _ => Nat) b a (Nat.ble a b)

@[expose] noncomputable def lnCrit (Lb x y : Nat) : Bool :=
  Nat.beq (Nat.land Lb (Nat.sub (Nat.shiftLeft 1 y) 1)) (Nat.shiftLeft 1 x)

@[expose] noncomputable def lnClq (UP PP : Nat) (PB : Nat → Nat) (x y : Nat) : Bool :=
  letB (Nat.land (PB x) (PB y)) fun A => letB (line3 UP PP x y) fun t =>
    allL [x, y, Nat.mod t 1024, Nat.mod (Nat.div t 1024) 1024, Nat.div t 1048576] fun z =>
      andB (bitK A z) (Nat.beq (Nat.land A (PB z)) A)

@[expose] noncomputable def lnFold (UP PP : Nat) (PB : Nat → Nat) (PL : Nat → List Nat) (x y : Nat) :
    Bool :=
  letB (PB y) fun Py => Nat.beq (List.rec (motive := fun _ => Nat) (Nat.sub (Nat.shiftLeft 1 693) 1)
    (fun w _ ih => Bool.rec (motive := fun _ => Nat) ih (Nat.land ih (PB w)) (bitK Py w)) (PL x))
    (lineB UP PP x y)

@[expose] noncomputable def lnRef (UP PP : Nat) (PB : Nat → Nat) (x y : Nat) : Bool :=
  letB (lineB UP PP x y) fun Lb => letB (line3 UP PP x y) fun t =>
    letB (Nat.mod t 1024) fun a => letB (Nat.mod (Nat.div t 1024) 1024) fun b =>
    letB (Nat.div t 1048576) fun c =>
    letB (lnMin x (lnMin y (lnMin a (lnMin b c)))) fun m1 =>
    letB (lnMin (Bool.rec (motive := fun _ => Nat) x 1024 (Nat.beq x m1))
      (lnMin (Bool.rec (motive := fun _ => Nat) y 1024 (Nat.beq y m1))
      (lnMin (Bool.rec (motive := fun _ => Nat) a 1024 (Nat.beq a m1))
      (lnMin (Bool.rec (motive := fun _ => Nat) b 1024 (Nat.beq b m1))
        (Bool.rec (motive := fun _ => Nat) c 1024 (Nat.beq c m1)))))) fun m2 =>
    andB (Nat.blt m1 m2) <| andB (Nat.blt m2 693) <| andB (bitK (PB m1) m2) <|
      andB (Nat.beq (lineB UP PP m1 m2) Lb) (lnCrit Lb m1 m2)

@[expose] noncomputable def lnChk (UP PP : Nat) (PB : Nat → Nat) (PL : Nat → List Nat) (x y : Nat) :
    Bool :=
  andB (line5 UP PP x y) <| andB (lnClq UP PP PB x y) <|
      Bool.rec (motive := fun _ => Bool) (lnRef UP PP PB x y) (lnFold UP PP PB PL x y)
        (lnCrit (lineB UP PP x y) x y)

@[expose] noncomputable def linesK (UP PP : Nat) (PB : Nat → Nat) (PL : Nat → List Nat) (lo n : Nat) :
    Bool :=
  allN n fun d => letB (Nat.add lo d) fun x => impB (Nat.blt x 693) <|
    allL (PL x) fun y => impB (Nat.blt x y) (lnChk UP PP PB PL x y)

@[expose] noncomputable def twinsK (UP PP : Nat) (PB : Nat → Nat) (PL : Nat → List Nat) : Bool :=
  letB (Nat.sub (PB 0) 1) fun D => allL (PL 0) fun x => impB (notB (Nat.beq x 0)) <|
    letB (Nat.land (PB x) D) fun Ax => letB (lineB UP PP 0 x) fun Lb =>
      allL (PL 0) fun y => impB (andB (notB (Nat.beq y 0)) (notB (Nat.beq y x))) <|
        Bool.rec (motive := fun _ => Bool) (notB (bitK Lb y)) (bitK Lb y)
          (Nat.beq (Nat.land (PB y) D) Ax)

@[expose] noncomputable def tv0 (UP PP q : Nat) : Nat :=
  at' 10 PP (normK (tvK (at' 12 UP 0) (at' 12 UP q)))

@[expose] noncomputable def ppNb (S : Nat) (l : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun p _ ih =>
    Bool.rec (motive := fun _ => List Nat) ih (List.cons p ih) (bitK S p)) l

@[expose] noncomputable def ppK (UP PP : Nat) (PB : Nat → Nat) (PL : Nat → List Nat) (lo n : Nat) :
    Bool :=
  letB (PB 0) fun P0 => allN n fun d => letB (Nat.add lo d) fun q =>
    impB (andB (Nat.blt q 693) (notB (bitK P0 q))) <| letB (Nat.land P0 (PB q)) fun Nb =>
    plK.letLN' (ppNb Nb (PL 0)) fun N =>
    andB (Nat.beq (lenN N) 45) <|
    andB (anyL N fun a => anyL N fun b =>
      andB (bitK (PB a) b) <| andB (notB (Nat.beq a b)) <|
        Nat.ble 3 (popK (Nat.land (lineB UP PP a b) Nb))) <|
    andB (allL N fun a => letB (Nat.land (PB a) Nb) fun Aa =>
      allL N fun b => impB (andB (bitK (PB a) b) (notB (Nat.beq a b)))
        (notB (Nat.beq (Nat.land (PB b) Nb) Aa))) <|
    letB (tv0 UP PP q) fun t => allN 693 fun q' => impB (notB (bitK P0 q')) <|
      impB (Nat.beq (Nat.land P0 (PB q')) Nb) (orB (Nat.beq q' q) (Nat.beq q' t))

end CFSG.KC.Misc.Lines

end
