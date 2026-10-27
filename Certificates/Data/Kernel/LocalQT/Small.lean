module

public import Certificates.Data.Kernel.LocalQT.Perm

public section

namespace CFSG.KC.LQT.S

open CFSG.KC.Ord CFSG.KC.LQT.P

@[expose] noncomputable def sw2 (n a b c d : Nat) : Nat := mul n (swap n a b) (swap n c d)

@[expose] noncomputable def memL (s : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun x _ ih => orB (Nat.beq s x) ih) l

@[expose] noncomputable def c4032a (ks : List Nat) : Bool :=
  allP 7 fun s => impB (Nat.beq (mul 7 s s) (one 7)) (impB (notB (Nat.beq s (one 7)))
    (memL (fix 7 s) ks))

@[expose] noncomputable def invCover (k : Nat) (l : List Nat) : Bool :=
  allP 7 fun s => impB (Nat.beq (mul 7 s s) (one 7)) (impB (Nat.beq (fix 7 s) k) (memL s l))

@[expose] noncomputable def p22 (s : Nat) : Bool :=
  anyC 7 s fun c => andB (even 7 c) (andB (Nat.beq (mul 7 (mul 7 c c) c) (one 7))
    (andB (notB (Nat.beq c (one 7)))
      (allC 7 s fun g => impB (even 7 g)
        (orB (Nat.beq (conj 7 g c) c) (Nat.beq (conj 7 g c) (inv 7 c))))))

@[expose] noncomputable def q2 (s : Nat) : Bool :=
  allC 7 s fun x => impB (even 7 x) (impB (Nat.beq (mul 7 x x) (one 7))
    (impB (notB (Nat.beq x (one 7)))
      (anyC 7 s fun g => andB (even 7 g)
        (andB (Nat.beq (pow 7 (mul 7 x (conj 7 g x)) 3) (one 7))
          (notB (Nat.beq (mul 7 x (conj 7 g x)) (one 7)))))))

@[expose] noncomputable def c4032d (k : Nat) : Bool :=
  allP 7 fun s => impB (Nat.beq (mul 7 s s) (one 7)) (impB (Nat.beq (fix 7 s) k)
    (anyC 7 s fun c => andB (even 7 c) (notB (Nat.beq c (one 7)))))

@[expose] noncomputable def commL (n t : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => andB (comm n t x) ih) l

@[expose] noncomputable def c4032e (ts : List Nat) : Bool :=
  allP 7 fun t => impB (commL 7 t ts) (Nat.beq t (one 7))

@[expose] noncomputable def iffB (p q : Bool) : Bool := Bool.rec (motive := fun _ => Bool) (notB q) q p

@[expose] noncomputable def fstP (w : Nat) : Nat := Nat.land w (Nat.sub (Nat.shiftLeft 1 40) 1)

@[expose] noncomputable def sndP (w : Nat) : Nat := Nat.shiftRight w 40

@[expose] noncomputable def distinctL (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x xs ih => andB (notB (memL x xs)) ih) l

@[expose] noncomputable def ptK (a b i : Nat) : Nat :=
  CFSG.KC.Loop.strictN (Bool.rec (motive := fun _ => Nat) b a (Nat.blt a b)) fun lo =>
  CFSG.KC.Loop.strictN (Bool.rec (motive := fun _ => Nat) a b (Nat.blt a b)) fun hi =>
  CFSG.KC.Loop.strictN (Bool.rec (motive := fun _ => Nat) i (Nat.succ i) (Nat.ble lo i)) fun v =>
    Bool.rec (motive := fun _ => Nat) v (Nat.succ v) (Nat.ble hi v)

@[expose] noncomputable def g5K (a b : Nat) : Nat :=
  mul 8 (mul 8 (mul 8 (swap 8 (ptK a b 0) (ptK a b 1)) (swap 8 (ptK a b 1) (ptK a b 2)))
    (swap 8 (ptK a b 2) (ptK a b 3))) (swap 8 (ptK a b 3) (ptK a b 4))

@[expose] noncomputable def g3K (a b : Nat) : Nat :=
  mul 8 (swap 8 (ptK a b 3) (ptK a b 4)) (swap 8 (ptK a b 4) (ptK a b 5))

@[expose] noncomputable def c4044 (G5 G3 : Nat → Nat → Nat) : Bool :=
  allN 8 fun a => allN 8 fun b => impB (notB (Nat.beq a b))
    (letB (G5 a b) fun g5 => letB (G3 a b) fun g3 =>
      allC 8 g5 fun t => impB (comm 8 t g3) (orB (Nat.beq t (one 8)) (Nat.beq t (swap 8 a b))))

@[expose] noncomputable def kom (n x s : Nat) : Nat := mul n (mul n (mul n (inv n x) (inv n s)) x) s

@[expose] noncomputable def c4100 (A : Nat) : Bool :=
  andB (allP 6 fun t => impB (even 6 t) (impB (Nat.beq (mul 6 t t) (one 6))
    (impB (notB (Nat.beq t (one 6))) (anyP 6 fun g => andB (even 6 g) (Nat.beq (conj 6 g A) t)))))
  (andB (allP 6 fun g => impB (Nat.beq (pow 6 g 9) (one 6)) (Nat.beq (pow 6 g 3) (one 6)))
    (allN 6 fun a => allN 6 fun b => impB (notB (Nat.beq a b)) (letB (swap 6 a b) fun s =>
      anyP 6 fun x => andB (even 6 x) (letB (kom 6 x s) fun c =>
        andB (Nat.beq (mul 6 c c) (one 6)) (notB (Nat.beq c (one 6)))))))

@[expose] noncomputable def c4156 (A : Nat) (w1 w3 : List Nat) : Bool :=
  andB (allP 7 fun t => impB (even 7 t) (impB (Nat.beq (mul 7 t t) (one 7))
    (impB (notB (Nat.beq t (one 7))) (anyL w1 fun w => Nat.beq (fstP w) t))))
  (andB (allL w1 fun w => andB (permK 7 (sndP w)) (andB (even 7 (sndP w))
    (Nat.beq (conj 7 (sndP w) A) (fstP w))))
  (andB (allP 7 fun g => impB (Nat.beq (pow 7 g 9) (one 7)) (Nat.beq (pow 7 g 3) (one 7)))
  (andB (allP 7 fun s => impB (Nat.beq (mul 7 s s) (one 7)) (impB (Nat.beq (fix 7 s) 1)
    (anyL w3 fun w => Nat.beq (fstP w) s)))
    (allL w3 fun w => andB (Nat.beq (mul 7 (fstP w) (fstP w)) (one 7))
      (andB (Nat.beq (fix 7 (fstP w)) 1) (andB (permK 7 (sndP w)) (andB (even 7 (sndP w))
        (letB (kom 7 (sndP w) (fstP w))
          fun c => andB (Nat.beq (mul 7 c c) (one 7)) (notB (Nat.beq c (one 7)))))))))))

@[expose] noncomputable def c4122 (C1 C2 : Nat) : Bool :=
  allC 7 C1 fun s => impB (comm 7 s C2) (Nat.beq (pow 7 s 2) (one 7))

@[expose] noncomputable def c4129 (C5 C7 : Nat) : Bool :=
  andB (even 7 C5) (andB (even 7 C7) (andB (Nat.beq (pow 7 C5 5) (one 7))
  (andB (Nat.beq (pow 7 C7 7) (one 7)) (andB (notB (Nat.beq C5 (one 7)))
  (andB (notB (Nat.beq C7 (one 7)))
  (andB (Nat.beq (cntP 7 fun g => andB (even 7 g) (memL (conj 7 g C5)
      [one 7, C5, pow 7 C5 2, pow 7 C5 3, pow 7 C5 4])) 20)
    (Nat.beq (cntP 7 fun g => andB (even 7 g) (memL (conj 7 g C7)
      [one 7, C7, pow 7 C7 2, pow 7 C7 3, pow 7 C7 4, pow 7 C7 5, pow 7 C7 6])) 21)))))))

@[expose] noncomputable def stOK (B C acc pos v : Nat) : Bool :=
  allN pos fun i => andB
    (iffB (Nat.beq (img B i) (img B pos)) (Nat.beq (img B (img acc i)) (img B v)))
    (iffB (Nat.beq (img C i) (img C pos)) (Nat.beq (img C (img acc i)) (img C v)))

@[expose] noncomputable def cntSt (n B C : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun _ _ _ => 1)
    (fun _ ih pos mask acc =>
      Nat.rec (motive := fun _ => Nat) 0
        (fun v rest => Nat.add
          (Bool.rec (motive := fun _ => Nat)
            (Bool.rec (motive := fun _ => Nat) 0
              (ih (Nat.succ pos) (Nat.lor mask (Nat.shiftLeft 1 v))
                (Nat.add acc (Nat.shiftLeft v (Nat.mul 5 pos))))
              (stOK B C acc pos v))
            0 (Nat.blt 0 (Nat.land mask (Nat.shiftLeft 1 v))))
          rest) n) n 0 0 0

@[expose] noncomputable def c4138 (X7 Y7 X8 Y8 : Nat) : Bool :=
  andB (Nat.beq (cntSt 7 X7 Y7) 48) (Nat.beq (cntSt 8 X8 Y8) 128)

@[expose] noncomputable def syl (X Y Z : Nat) : List Nat :=
  [one 7, X, Y, mul 7 X Y, Z, mul 7 X Z, mul 7 Y Z, mul 7 (mul 7 X Y) Z]

@[expose] noncomputable def kle (X Y : Nat) : List Nat := [one 7, X, Y, mul 7 X Y]

@[expose] noncomputable def subOK (l : List Nat) (m : Nat) : Bool :=
  andB (allL l fun a => allL l fun b => memL (mul 7 a b) l)
  (andB (allL l fun a => memL (inv 7 a) l) (andB (memL (one 7) l)
  (andB (Nat.beq (List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => Nat.succ ih) l) m)
  (andB (distinctL l) (allL l fun a => even 7 a)))))

@[expose] noncomputable def c4128 (X Y Z : Nat) : Bool :=
  andB (subOK (syl X Y Z) 8) (andB (subOK (kle X Y) 4)
  (andB (allL (kle X Y) fun a => memL a (syl X Y Z))
  (andB (allP 7 fun g => impB (even 7 g) (impB (memL (conj 7 g X) (syl X Y Z))
    (impB (memL (conj 7 g Y) (syl X Y Z)) (impB (memL (conj 7 g Z) (syl X Y Z))
      (memL g (syl X Y Z))))))
  (andB (allP 7 fun g => impB (even 7 g) (impB (memL (conj 7 g X) (syl X Y Z))
    (impB (memL (conj 7 g Y) (syl X Y Z))
      (andB (memL (conj 7 g X) (kle X Y)) (memL (conj 7 g Y) (kle X Y))))))
  (andB (Nat.beq (cntP 7 fun g => andB (even 7 g)
      (andB (memL (conj 7 g X) (kle X Y)) (memL (conj 7 g Y) (kle X Y)))) 72)
    (notB (comm 7 Z Y)))))))

@[expose] noncomputable def lenL (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => Nat.succ ih) l

@[expose] noncomputable def grpL (l : List Nat) : Bool :=
  andB (memL (one 7) l) (andB (allL l fun x => allL l fun y => memL (mul 7 x y) l)
    (allL l fun x => memL (inv 7 x) l))

@[expose] noncomputable def allBs (l : List Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun b _ ih => andB b ih) l

@[expose] noncomputable def c4152l (P V K T : List Nat) (A B C1 C2 : Nat) : Bool := allBs
  [allL P (even 7), allL V (even 7), allL K (even 7), allL T (even 7),
   even 7 A, even 7 B, even 7 C1, even 7 C2,
   grpL P, grpL V, grpL K, grpL T,
   allL V (fun x => memL x P), allL P (fun x => memL x K),
   distinctL P, Nat.beq (lenL P) 8, distinctL V, Nat.beq (lenL V) 4,
   distinctL K, Nat.beq (lenL K) 24, distinctL T, Nat.beq (lenL T) 3,
   allL K (fun k => allL V fun v => memL (conj 7 k v) V),
   allL K (fun k => impB (allL V fun v => comm 7 k v) (memL k V)),
   anyL K (fun k => anyL P fun p => notB (memL (conj 7 k p) P)),
   notB (Nat.beq A (one 7)), notB (Nat.beq B (one 7)), notB (Nat.beq A B), comm 7 A B,
   Nat.beq (mul 7 A A) (one 7), Nat.beq (mul 7 B B) (one 7),
   notB (Nat.beq C2 (one 7)), Nat.beq (pow 7 C2 3) (one 7),
   notB (Nat.beq C1 (one 7)), Nat.beq (pow 7 C1 3) (one 7),
   comm 7 C2 A, comm 7 C2 B, memL C1 K, notB (memL C1 T), memL C2 T, memL A V, memL B V,
   allL P fun u1 => allL P fun u2 => impB (notB (Nat.beq u1 (one 7)))
    (impB (notB (Nat.beq u2 (one 7))) (impB (notB (Nat.beq u1 u2)) (impB (comm 7 u1 u2)
    (impB (Nat.beq (mul 7 u1 u1) (one 7)) (impB (Nat.beq (mul 7 u2 u2) (one 7))
    (impB (anyC 7 u1 fun x => andB (even 7 x) (andB (notB (Nat.beq x (one 7)))
        (andB (Nat.beq (pow 7 x 3) (one 7)) (comm 7 x u2))))
      (andB (memL u1 V) (memL u2 V))))))))]

@[expose] noncomputable def c4152s (V K T : List Nat) (C1 C2 : Nat) : Bool :=
  andB (allP 7 fun t => impB (Nat.beq (pow 7 t 2) (one 7)) (impB (Nat.beq (fix 7 t) 1)
    (anyL K fun k => notB (comm 7 k t))))
  (andB (allP 7 fun x => impB (even 7 x) (impB (Nat.beq (pow 7 x 3) (one 7))
    (impB (allL V fun v => comm 7 x v) (memL x T))))
  (andB (allL T fun y => impB (notB (Nat.beq y (one 7)))
    (anyP 7 fun g => andB (even 7 g) (Nat.beq (conj 7 g C2) y)))
  (andB (anyP 7 fun g => andB (even 7 g) (Nat.beq (conj 7 g C2) C1))
    (allP 7 fun y => impB (even 7 y) (impB (Nat.beq (pow 7 y 3) (one 7))
      (impB (notB (Nat.beq y (one 7))) (impB (allL V fun v => memL (conj 7 y v) V)
      (impB (notB (memL y T)) (impB (anyP 7 fun g => andB (even 7 g) (Nat.beq (conj 7 g C2) y))
        (memL y K))))))))))

@[expose] noncomputable def c4095 (G H U T : List Nat) : Bool :=
  andB (allL G fun g => allL H fun x => andB (memL (mul 6 g x) H) (memL (mul 6 (inv 6 g) x) H))
  (andB (allL U fun g => allL T fun x => andB (memL (mul 6 g x) T) (memL (mul 6 (inv 6 g) x) T))
    (allL H fun x => impB (allL U fun t => memL (conj 6 x t) T) (memL x T)))

@[expose] noncomputable def dedupL (l : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun x _ ih acc => ih (Bool.rec (motive := fun _ => List Nat) (List.cons x acc) acc (memL x acc)))
    l []

@[expose] noncomputable def filtL (l : List Nat) (f : Nat → Bool) : List Nat :=
  List.rec (motive := fun _ => List Nat) []
    (fun x _ ih => Bool.rec (motive := fun _ => List Nat) ih (List.cons x ih) (f x)) l

@[expose] noncomputable def commsL (n : Nat) (l : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) []
    (fun y _ ih => List.rec (motive := fun _ => List Nat) ih
      (fun w _ ih2 => List.cons (mul n (mul n (mul n y w) (inv n y)) (inv n w)) ih2) l) l

@[expose] noncomputable def getK (l : List Nat) (i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun x _ ih j => Bool.rec (motive := fun _ => Nat) (ih (Nat.sub j 1)) x (Nat.beq j 0)) l i

@[expose] noncomputable def c4046v (LP V : List Nat) (T0 G0 : Nat) : Bool := allBs
  [memL (one 8) LP, allL LP (fun a => allL LP fun b => memL (mul 8 a b) LP),
   allL LP (fun a => memL (inv 8 a) LP), allL LP (even 8), distinctL LP, Nat.beq (lenL LP) 64,
   notB (Nat.beq (getK V 1) (one 8)),
   allC 8 (getK V 1) (fun x => impB (allL V fun v => comm 8 x v) (memL x V)),
   notB (Nat.beq (getK LP 1) (one 8)),
   allC 8 (getK LP 1) (fun x => impB (notB (Nat.beq x (one 8)))
     (impB (allL LP fun p => comm 8 x p) (Nat.beq x T0))),
   allL V (fun v => memL (mul 8 (mul 8 G0 v) (inv 8 G0)) V),
   allL V (fun v => memL (mul 8 (mul 8 (inv 8 G0) v) G0) V),
   notB (comm 8 G0 T0), even 8 G0]

@[expose] noncomputable def eqLs (l m : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun m => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) m)
    (fun x _ ih m => List.rec (motive := fun _ => Bool) false
      (fun y ys _ => andB (Nat.beq x y) (ih ys)) m) l m

@[expose] noncomputable def c4046 (LP V : List Nat) (T0 G0 : Nat) : Bool :=
  andB (eqLs V (filtL LP fun x => allL (dedupL (commsL 8 LP)) fun c => comm 8 x c))
    (c4046v LP V T0 G0)

@[expose] noncomputable def c4153 (L Q : List Nat) : Bool :=
  andB (eqLs Q (filtL L fun x => Nat.beq (pow 10 x 45) (one 10)))
    (allL L fun x => orB (Nat.beq x (one 10)) (orB (notB (memL x Q))
      (allL L fun u => orB (notB (comm 10 u x)) (memL u Q))))

@[expose] noncomputable def sumMask (l : List Nat) (m : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun x _ ih i => Nat.add (Bool.rec (motive := fun _ => Nat) 0 x
      (Nat.blt 0 (Nat.land m (Nat.shiftLeft 1 i)))) (ih (Nat.succ i))) l 0

@[expose] noncomputable def c4147 (l : List Nat) (k N : Nat) : Bool :=
  andB (Nat.beq (lenL l) k)
    (allN (Nat.shiftLeft 1 (Nat.sub k 1)) fun h => letB (Nat.add (Nat.shiftLeft h 1) 1) fun m =>
      impB (Nat.beq (Nat.mod N (sumMask l m)) 0)
        (orB (Nat.beq m 1) (Nat.beq m (Nat.sub (Nat.shiftLeft 1 k) 1))))

end CFSG.KC.LQT.S

end
