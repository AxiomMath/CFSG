module

public import CFSG.Certificates.Kernel.Orders.Mat

public section

namespace CFSG.KC.C7155

open CFSG.KC.Loop CFSG.KC.Ord

@[expose] noncomputable def allN (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i ih => andB (f i) ih) n

@[expose] noncomputable def anyN (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun i ih => orB (f i) ih) n

@[expose] noncomputable def anyL (L : List Nat) (f : Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun t _ ih => orB (f t) ih) L

@[expose] noncomputable def strictB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def ent (M s : Nat) : Nat := Nat.land (Nat.shiftRight M s) 7

@[expose] noncomputable def d3 (a b c x y z : Nat) : Nat :=
  Nat.mod (Nat.add (Nat.add (Nat.mul a x) (Nat.mul b y)) (Nat.mul c z)) 5

@[expose] noncomputable def pk9 (a0 a1 a2 a3 a4 a5 a6 a7 a8 : Nat) : Nat :=
  Nat.add a0 (Nat.add (Nat.shiftLeft a1 3) (Nat.add (Nat.shiftLeft a2 6)
    (Nat.add (Nat.shiftLeft a3 9) (Nat.add (Nat.shiftLeft a4 12) (Nat.add (Nat.shiftLeft a5 15)
      (Nat.add (Nat.shiftLeft a6 18) (Nat.add (Nat.shiftLeft a7 21) (Nat.shiftLeft a8 24))))))))

@[expose] noncomputable def mul9 (a0 a1 a2 a3 a4 a5 a6 a7 a8 b0 b1 b2 b3 b4 b5 b6 b7 b8 : Nat) :
    Nat :=
  pk9 (d3 a0 a1 a2 b0 b3 b6) (d3 a0 a1 a2 b1 b4 b7) (d3 a0 a1 a2 b2 b5 b8)
    (d3 a3 a4 a5 b0 b3 b6) (d3 a3 a4 a5 b1 b4 b7) (d3 a3 a4 a5 b2 b5 b8)
    (d3 a6 a7 a8 b0 b3 b6) (d3 a6 a7 a8 b1 b4 b7) (d3 a6 a7 a8 b2 b5 b8)

@[expose] noncomputable def mulM (A B : Nat) : Nat :=
  strictN A fun A => strictN B fun B =>
    mul9 (ent A 0) (ent A 3) (ent A 6) (ent A 9) (ent A 12) (ent A 15) (ent A 18) (ent A 21)
      (ent A 24) (ent B 0) (ent B 3) (ent B 6) (ent B 9) (ent B 12) (ent B 15) (ent B 18)
      (ent B 21) (ent B 24)

@[expose] noncomputable def idM : Nat := 16781313

@[expose] noncomputable def inT (M : Nat) : Bool :=
  andB (Nat.beq (Nat.land M 16744896) 0) (andB (notB (Nat.beq (ent M 24) 0))
    (orB (andB (Nat.beq (Nat.land M 3640) 0)
        (andB (notB (Nat.beq (ent M 0) 0)) (notB (Nat.beq (ent M 12) 0))))
      (andB (Nat.beq (Nat.land M 28679) 0)
        (andB (notB (Nat.beq (ent M 3) 0)) (notB (Nat.beq (ent M 9) 0))))))

@[expose] noncomputable def tC : List Nat :=
  [16781313, 67109384, 50339841, 33555464, 33566721, 50333192, 67125249, 16779272, 50335746,
    33554960, 67117058, 16778256, 16789506, 67110416, 33570818, 50333712, 33558531, 50332184,
    16785411, 67109912, 67121155, 16778776, 50348035, 33556504, 67112964, 16777760, 33562628,
    50332704, 50343940, 33556000, 16793604, 67110944]

@[expose] noncomputable def refAux (A u : Nat) (k : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ ih g => andB (notB (inT (mulM g u))) (ih (mulM A g))) k

@[expose] noncomputable def refute (L : List Nat) (A o : Nat) : Bool :=
  anyL L fun t => refAux A (mulM t A) o idM

@[expose] noncomputable def pow5M (A : Nat) : Nat :=
  strictN (mulM A A) fun A2 => strictN (mulM A2 A2) fun A4 => mulM A4 A

@[expose] noncomputable def levElt (L : List Nat) (a b c d e f : Nat) : Bool :=
  orB (notB (Nat.beq (Nat.mod (Nat.add (Nat.mul a d) (Nat.mul 4 (Nat.mul b c))) 5) 1))
    (strictB (pk9 a b 0 c d 0 e f 1) fun g =>
      orB (Nat.beq g idM) (orB (notB (Nat.beq (pow5M g) idM)) (refute L g 5)))

@[expose] noncomputable def levOKL (L : List Nat) : Bool :=
  allN 5 fun a => allN 5 fun b => allN 5 fun c => allN 5 fun d => levElt L a b c d 0 0

@[expose] noncomputable def inv5 (a : Nat) : Nat := Nat.mod (Nat.mul a (Nat.mul a a)) 5

@[expose] noncomputable def img (M x y : Nat) : Nat :=
  strictN M fun M =>
    strictN (inv5 (d3 (ent M 18) (ent M 21) (ent M 24) x y 1)) fun w =>
      Nat.add (Nat.mul 5 (Nat.mod (Nat.mul (d3 (ent M 0) (ent M 3) (ent M 6) x y 1) w) 5))
        (Nat.mod (Nat.mul (d3 (ent M 9) (ent M 12) (ent M 15) x y 1) w) 5)

@[expose] noncomputable def neB (a b : Nat) : Bool := notB (Nat.beq a b)

@[expose] noncomputable def dist5 (p0 p1 p2 p3 p4 : Nat) : Bool :=
  andB (andB (neB p0 p1) (andB (neB p0 p2) (andB (neB p0 p3) (neB p0 p4))))
    (andB (andB (neB p1 p2) (andB (neB p1 p3) (neB p1 p4)))
      (andB (andB (neB p2 p3) (neB p2 p4)) (neB p3 p4)))

@[expose] noncomputable def ptElt (L : List Nat) (x y : Nat) : Bool :=
  orB (andB (Nat.beq x 0) (Nat.beq y 0))
    (anyL L fun t => dist5 (img idM x y) (img 67117058 x y) (img 67121155 x y)
      (img 16793604 x y) (img t x y))

@[expose] noncomputable def ptOKL (L : List Nat) : Bool :=
  allN 5 fun x => allN 5 fun y => ptElt L x y

@[expose] noncomputable def pk3 (a0 a1 a2 : Nat) : Nat :=
  Nat.add a0 (Nat.add (Nat.shiftLeft a1 3) (Nat.shiftLeft a2 6))

@[expose] noncomputable def mul3 (t c a0 a1 a2 b0 b1 b2 : Nat) : Nat :=
  strictN (Nat.mul a0 b0) fun p0 =>
  strictN (Nat.add (Nat.mul a0 b1) (Nat.mul a1 b0)) fun p1 =>
  strictN (Nat.add (Nat.add (Nat.mul a0 b2) (Nat.mul a1 b1)) (Nat.mul a2 b0)) fun p2 =>
  strictN (Nat.add (Nat.mul a1 b2) (Nat.mul a2 b1)) fun p3 =>
  strictN (Nat.mul a2 b2) fun p4 =>
    pk3 (Nat.mod (Nat.add (Nat.add p0 p3) (Nat.mul t p4)) 5)
      (Nat.mod (Nat.add (Nat.add p1 (Nat.mul (Nat.mul 4 c) p3))
        (Nat.mul (Nat.add (Nat.mul 4 (Nat.mul t c)) 1) p4)) 5)
      (Nat.mod (Nat.add (Nat.add p2 (Nat.mul t p3)) (Nat.mul (Nat.add (Nat.mul t t) (Nat.mul 4 c)) p4))
        5)

@[expose] noncomputable def mulQ (t c P Q : Nat) : Nat :=
  strictN P fun P => strictN Q fun Q =>
    mul3 t c (ent P 0) (ent P 3) (ent P 6) (ent Q 0) (ent Q 3) (ent Q 6)

@[expose] noncomputable def powQ (t c : Nat) (bits : List Bool) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun r => r)
    (fun b _ ih r => ih (strictN (mulQ t c r r) fun s =>
      Bool.rec (motive := fun _ => Nat) s (mulQ t c s 8) b)) bits 1

@[expose] noncomputable def subOne (P : Nat) : Nat :=
  Nat.add (Nat.mod (Nat.add (ent P 0) 4) 5) (Nat.sub P (ent P 0))

@[expose] noncomputable def chiAt (t c l : Nat) : Nat :=
  Nat.mod (Nat.add (Nat.add (Nat.mul l (Nat.mul l l)) (Nat.mul (Nat.mul 4 t) (Nat.mul l l)))
    (Nat.add (Nat.mul c l) 4)) 5

@[expose] def bits11625 : List Bool :=
  [true, false, true, true, false, true, false, true, true, false, true, false, false, true]

@[expose] def bits31 : List Bool := [true, true, true, true, true]

@[expose] noncomputable def bucketOK (bits : List Bool) (t c : Nat) : Bool :=
  orB (strictB (subOne (powQ t c bits)) fun y =>
      anyN 5 fun u0 => anyN 5 fun u1 => anyN 5 fun u2 =>
        Nat.beq (mulQ t c (pk3 u0 u1 u2) y) (pk3 0 (Nat.mod (Nat.mul 4 c) 5) t))
    (orB (andB (Nat.beq (powQ t c bits31) 1) (allN 5 fun l => notB (Nat.beq (chiAt t c l) 0)))
      (andB (Nat.beq t 3) (Nat.beq c 3)))

@[expose] noncomputable def bucketsOK (bits : List Bool) : Bool :=
  allN 5 fun t => allN 5 fun c => bucketOK bits t c

end CFSG.KC.C7155

end
