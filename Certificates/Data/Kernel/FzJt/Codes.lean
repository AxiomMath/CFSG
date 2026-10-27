module

public import Init

@[expose] public noncomputable section

namespace Certificates.FzJt.K

def bA (a b : Bool) : Bool := Bool.rec false b a
def bO (a b : Bool) : Bool := Bool.rec b true a
def bI (a b : Bool) : Bool := Bool.rec true b a
def bN (a : Bool) : Bool := Bool.rec true false a

def QT : Nat := 1673236477377915207467858097797159432941933252272604235400
def ZM : Nat := 30978574250111236308116032539271932298602835806837157437180626681198887498742984880503380596607288335858378028087498815490146080688503245390422004857715631302156672429260804

def qm (a b : Nat) : Nat := Nat.land (Nat.shiftRight QT (Nat.mul 3 (Nat.add (Nat.mul 8 a) b))) 7
def nz (c : Nat) : Nat := Nat.xor c (Nat.mul 146 (Nat.land (Nat.shiftRight c 7) 1))
def mk (x y z e : Nat) : Nat :=
  Nat.add x (Nat.add (Nat.mul 8 y) (Nat.add (Nat.mul 64 z) (Nat.mul 512 e)))
def sw (e x y : Nat) : Nat := Bool.rec y x (Nat.beq e 0)
def mul8 (a1 b1 c1 e1 a2 b2 c2 e2 : Nat) : Nat :=
  nz (mk (qm a1 (sw e1 a2 b2)) (qm b1 (sw e1 b2 a2)) (qm c1 c2) (Nat.xor e1 e2))
def mul5 (a1 b1 c1 e1 d : Nat) : Nat :=
  mul8 a1 b1 c1 e1 (Nat.land d 7) (Nat.land (Nat.shiftRight d 3) 7)
    (Nat.land (Nat.shiftRight d 6) 7) (Nat.shiftRight d 9)
def mulK (c d : Nat) : Nat :=
  mul5 (Nat.land c 7) (Nat.land (Nat.shiftRight c 3) 7) (Nat.land (Nat.shiftRight c 6) 7)
    (Nat.shiftRight c 9) d

def rep (t : Nat) : Nat := Nat.add (Nat.land t 127) (Nat.shiftLeft (Nat.shiftRight t 7) 8)
def isC (c : Nat) : Bool := bA (Nat.blt c 1024) (Nat.beq (Nat.land c 128) 0)
def inZK (c : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight ZM c) 1) 1
def commK (a b : Nat) : Bool := Nat.beq (mulK a b) (mulK b a)

def filterR (n : Nat) (p : Nat → Bool) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) []
    (fun t acc => Bool.rec acc (List.cons (rep t) acc) (p (rep t))) n
def filterL (L : List Nat) (p : Nat → Bool) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun x _ acc => Bool.rec acc (List.cons x acc) (p x)) L
def allL (L : List Nat) (f : Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ acc => bA (f x) acc) L
def anyL (L : List Nat) (f : Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun x _ acc => bO (f x) acc) L
def allR (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun t acc => bA (f (rep t)) acc) n
def anyN (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun i acc => bO (f i) acc) n
def eqL (l₁ : List Nat) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun l => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) l)
    (fun x _ ih l => List.rec (motive := fun _ => Bool) false (fun y t _ => bA (Nat.beq x y) (ih t)) l)
    l₁
def memL (x : Nat) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun y _ acc => bO (Nat.beq x y) acc) L
def lowL (L : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun x _ acc => List.cons (Nat.land x 1023) acc) L
def heads (R : List (List Nat)) : List Nat :=
  List.rec (motive := fun _ => List Nat) []
    (fun r _ acc => List.rec (motive := fun _ => List Nat) acc (fun v _ _ => List.cons v acc) r) R
def allRows (R : List (List Nat)) (f : List Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun r _ acc => bA (f r) acc) R

def sqOK (uu s : Nat) : Bool := bO (Nat.beq s 0) (Nat.beq s uu)
def f2W (uu v : Nat) (Cv : List Nat) (w : Nat) : Bool :=
  bI (Nat.beq (mulK (mulK v w) v) w) (allL Cv (fun y => bI (commK y w) (sqOK uu (mulK y y))))
def f2Row (uu : Nat) (C S : List Nat) (r : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun v Cv _ => bA (eqL (filterL C (fun y => commK y v)) Cv) (allL S (f2W uu v Cv))) r
def f2B (u : Nat) (C S : List Nat) (SV : List (List Nat)) : Bool :=
  bA (eqL (filterR 512 (fun c => commK c u)) C)
    (bA (eqL (filterL C (fun v => Nat.beq (mulK v v) (mulK u u))) S)
      (bA (eqL (heads SV) S) (allRows SV (f2Row (mulK u u) C S))))

def f3L (L : List Nat) : Bool :=
  allL L (fun v => allL L (fun w =>
    bO (Nat.beq v w) (bO (bN (commK v w)) (bO (inZK v) (bO (inZK w) (inZK (mulK v w)))))))
def p3 (a c : Nat) : Bool := bA (Nat.beq (mulK c c) 0) (bA (bN (Nat.beq c 0)) (commK c a))
def f3B (a : Nat) (L : List Nat) : Bool := bA (eqL (filterR 512 (p3 a)) L) (f3L L)

def r3c (i : Nat) : Nat := nz (Nat.mul 64 i)
def zs4K : List Nat := [0, 2, 18, mulK 2 18]
def domK (n : Nat) : Bool :=
  bA (Nat.beq (mulK n n) 18)
    (bA (bN (anyN 8 (fun i => Nat.beq n (r3c i))))
      (bO (Nat.beq (Nat.shiftRight n 9) 1)
        (anyN 8 (fun i => anyL zs4K (fun z => Nat.beq n (mulK (r3c i) z))))))
def invNZ (c : Nat) : Bool :=
  bA (isC c) (bA (Nat.beq (mulK c c) 0) (bA (bN (Nat.beq c 0)) (bN (inZK c))))
def witK (x : Nat) : Bool :=
  bA (Nat.blt x 1073741824)
    (bA (commK (Nat.land (Nat.shiftRight x 10) 1023) (Nat.land x 1023))
      (bA (commK (Nat.shiftRight x 20) (Nat.land x 1023))
        (bA (invNZ (Nat.land (Nat.shiftRight x 10) 1023))
          (bA (invNZ (Nat.shiftRight x 20))
            (bA (bN (Nat.beq (Nat.land (Nat.shiftRight x 10) 1023) (Nat.shiftRight x 20)))
              (bA (commK (Nat.land (Nat.shiftRight x 10) 1023) (Nat.shiftRight x 20))
                (bN (inZK (mulK (Nat.land (Nat.shiftRight x 10) 1023) (Nat.shiftRight x 20))))))))))
def f4B (W : List Nat) : Bool :=
  bA (allR 512 (fun c => bI (domK c) (memL c (lowL W)))) (allL W witK)

end Certificates.FzJt.K
