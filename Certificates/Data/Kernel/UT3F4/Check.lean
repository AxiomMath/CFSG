module

public section

namespace CFSG.Certificates.Kernel.UT3F4

@[expose] noncomputable def orB (x y : Bool) : Bool := Bool.rec y true x

@[expose] noncomputable def andB (x y : Bool) : Bool := Bool.rec false y x

@[expose] noncomputable def notB (x : Bool) : Bool := Bool.rec true false x

@[expose] noncomputable def letN (v : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) v

@[expose] noncomputable def allL (L : List Nat) (f : Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => andB (f x) ih) L

@[expose] noncomputable def anyL (L : List Nat) (f : Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun x _ ih => orB (f x) ih) L

@[expose] noncomputable def cntL (L : List Nat) (f : Nat → Bool) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun x _ ih => Bool.rec ih (Nat.succ ih) (f x)) L

@[expose] noncomputable def FT : Nat := nat_lit 2625168384

@[expose] noncomputable def fmN (u v : Nat) : Nat :=
  Nat.land (Nat.shiftRight FT (Nat.add (Nat.shiftLeft u 3) (Nat.shiftLeft v 1))) 3

@[expose] noncomputable def mulN (x y : Nat) : Nat :=
  Nat.xor (Nat.xor x y) (Nat.shiftLeft (fmN (Nat.land x 3) (Nat.land (Nat.shiftRight y 2) 3)) 4)

@[expose] noncomputable def sel4 (k v0 v1 v2 v3 : Nat) : Nat :=
  Bool.rec (Bool.rec (Bool.rec v3 v2 (Nat.beq k 2)) v1 (Nat.beq k 1)) v0 (Nat.beq k 0)

@[expose] noncomputable def eA (x y a : Nat) : Nat := sel4 a 0 x y (mulN x y)

@[expose] noncomputable def eZ (x0 x1 x2 z : Nat) : Nat :=
  sel4 z 0 (mulN x0 (mulN x2 (mulN x0 x2))) (mulN x1 (mulN x2 (mulN x1 x2)))
    (mulN x0 (mulN x2 (mulN x0 (mulN x2 (mulN x1 (mulN x2 (mulN x1 x2)))))))

@[expose] noncomputable def evalN (x0 x1 x2 x3 g : Nat) : Nat :=
  mulN (mulN (eA x0 x1 (Nat.land g 3)) (eA x2 x3 (Nat.land (Nat.shiftRight g 2) 3)))
    (eZ x0 x1 x2 (Nat.xor (Nat.shiftRight g 4)
      (fmN (Nat.land g 3) (Nat.land (Nat.shiftRight g 2) 3))))

@[expose] noncomputable def allPN : List Nat :=
  [0, 16, 32, 48, 4, 20, 36, 52, 8, 24, 40, 56, 12, 28, 44, 60, 1, 17, 33, 49, 5, 21, 37, 53, 9, 25,
    41, 57, 13, 29, 45, 61, 2, 18, 34, 50, 6, 22, 38, 54, 10, 26, 42, 58, 14, 30, 46, 62, 3, 19, 35,
    51, 7, 23, 39, 55, 11, 27, 43, 59, 15, 31, 47, 63]

@[expose] noncomputable def invN : List Nat :=
  [0, 16, 32, 48, 4, 20, 36, 52, 8, 24, 40, 56, 12, 28, 44, 60, 1, 17, 33, 49, 2, 18, 34, 50, 3, 19,
    35, 51]

@[expose] noncomputable def commN (x y : Nat) : Bool := Nat.beq (mulN x y) (mulN y x)

@[expose] noncomputable def sqN (x y : Nat) : Nat := mulN (mulN x y) (mulN x y)

@[expose] noncomputable def relN (a b c d : Nat) : Bool :=
  andB (Nat.beq (sqN b c) (sqN a d)) (Nat.beq (sqN b d) (mulN (sqN a c) (sqN a d)))

@[expose] noncomputable def h1N (a b c d : Nat) : Bool :=
  andB (Nat.beq (evalN a b c d a) 1) (andB (Nat.beq (evalN a b c d b) 2)
    (andB (Nat.beq (evalN a b c d c) 4) (Nat.beq (evalN a b c d d) 8)))

@[expose] noncomputable def fixN (a b c d : Nat) : Bool :=
  Nat.beq (cntL allPN fun g => Nat.beq (evalN a b c d g) g) 8

@[expose] noncomputable def q8N (a b c d : Nat) : Bool :=
  Nat.beq (cntL allPN fun g => andB (Nat.beq (evalN a b c d g) g) (Nat.beq (mulN g g) 0)) 2

@[expose] noncomputable def autN (s0 s1 s2 s3 : Nat) : Bool :=
  andB (allL allPN fun g =>
      andB (Nat.beq (evalN s0 s1 s2 s3 (mulN g 1)) (mulN (evalN s0 s1 s2 s3 g) s0))
        (andB (Nat.beq (evalN s0 s1 s2 s3 (mulN g 2)) (mulN (evalN s0 s1 s2 s3 g) s1))
          (andB (Nat.beq (evalN s0 s1 s2 s3 (mulN g 4)) (mulN (evalN s0 s1 s2 s3 g) s2))
            (Nat.beq (evalN s0 s1 s2 s3 (mulN g 8)) (mulN (evalN s0 s1 s2 s3 g) s3)))))
    (allL allPN fun g => orB (notB (Nat.beq (evalN s0 s1 s2 s3 g) 0)) (Nat.beq g 0))

@[expose] noncomputable def intN (a b c d s0 s1 s2 s3 : Nat) : Bool :=
  andB (Nat.beq (evalN s0 s1 s2 s3 4) (evalN a b c d s0))
    (andB (Nat.beq (evalN s0 s1 s2 s3 12) (evalN a b c d s1))
      (andB (Nat.beq (evalN s0 s1 s2 s3 1) (evalN a b c d s2))
        (Nat.beq (evalN s0 s1 s2 s3 3) (evalN a b c d s3))))

@[expose] noncomputable def witN (a b c d : Nat) : Bool :=
  anyL invN fun p => anyL invN fun q => andB (commN p q)
    (letN (evalN a b c d p) fun s2 => letN (mulN s2 (evalN a b c d q)) fun s3 =>
      andB (autN p q s2 s3) (intN a b c d p q s2 s3))

@[expose] noncomputable def testN (a b c d : Nat) : Bool :=
  orB (notB (h1N a b c d)) (orB (notB (fixN a b c d)) (orB (notB (q8N a b c d)) (witN a b c d)))

@[expose] noncomputable def checkN : Bool :=
  allL invN fun a => allL invN fun b => orB (notB (commN a b)) (allL invN fun c =>
    orB (commN a c) (allL invN fun d => orB (notB (commN c d)) (orB (notB (relN a b c d))
      (testN a b c d))))

end CFSG.Certificates.Kernel.UT3F4

end
