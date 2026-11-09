module

public import Certificates.Data.Kernel.F4M3B
public import Certificates.Data.CFSGNative.Stroth15.GL5

public noncomputable section

namespace CFSG.KC.GL5B

open CFSG.KC.F4M3B (frcN frc pln)
open CFSG.CGT.Stroth77.GL5 (mulC powC good uvC tC uC rhoC idC evalList x0Words nonsing)

structure Ops (α : Type) where
  a : α → α → α
  o : α → α → α
  x : α → α → α
  t : α
  z : α
  bd : α → (α → α) → α

structure R5 (α : Type) where
  e0 : α
  e1 : α
  e2 : α
  e3 : α
  e4 : α

structure M5 (α : Type) where
  r0 : R5 α
  r1 : R5 α
  r2 : R5 α
  r3 : R5 α
  r4 : R5 α

variable {α : Type}

@[expose] def bitB (n j : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight n j) 1) 1

@[expose] def dot (o : Ops α) (s0 s1 s2 s3 s4 a0 a1 a2 a3 a4 : α) : α :=
  o.x (o.x (o.x (o.x (o.a s0 a0) (o.a s1 a1)) (o.a s2 a2)) (o.a s3 a3)) (o.a s4 a4)

@[expose] def rowK (o : Ops α) (s : R5 α) (A : M5 α) (k : R5 α → α) : α :=
  o.bd (dot o s.e0 s.e1 s.e2 s.e3 s.e4 A.r0.e0 A.r1.e0 A.r2.e0 A.r3.e0 A.r4.e0) fun y0 =>
  o.bd (dot o s.e0 s.e1 s.e2 s.e3 s.e4 A.r0.e1 A.r1.e1 A.r2.e1 A.r3.e1 A.r4.e1) fun y1 =>
  o.bd (dot o s.e0 s.e1 s.e2 s.e3 s.e4 A.r0.e2 A.r1.e2 A.r2.e2 A.r3.e2 A.r4.e2) fun y2 =>
  o.bd (dot o s.e0 s.e1 s.e2 s.e3 s.e4 A.r0.e3 A.r1.e3 A.r2.e3 A.r3.e3 A.r4.e3) fun y3 =>
  o.bd (dot o s.e0 s.e1 s.e2 s.e3 s.e4 A.r0.e4 A.r1.e4 A.r2.e4 A.r3.e4 A.r4.e4) fun y4 =>
  k ⟨y0, y1, y2, y3, y4⟩

@[expose] def mulK (o : Ops α) (A B : M5 α) (k : M5 α → α) : α :=
  rowK o B.r0 A fun r0 => rowK o B.r1 A fun r1 => rowK o B.r2 A fun r2 =>
  rowK o B.r3 A fun r3 => rowK o B.r4 A fun r4 => k ⟨r0, r1, r2, r3, r4⟩

@[expose] def sx (o : Ops α) (b : Bool) (acc v : α) : α :=
  Bool.rec (motive := fun _ => α) acc (o.x acc v) b

@[expose] def sel (o : Ops α) (s : Nat) (v0 v1 v2 v3 v4 : α) : α :=
  sx o (bitB s 4) (sx o (bitB s 3) (sx o (bitB s 2) (sx o (bitB s 1) (sx o (bitB s 0) o.z v0) v1)
    v2) v3) v4

@[expose] def rowN (c i : Nat) : Nat := Nat.land (Nat.shiftRight c (Nat.mul 5 i)) 31

@[expose] def colN (c k : Nat) : Nat :=
  Nat.lor (Nat.land (Nat.shiftRight c k) 1)
    (Nat.lor (Nat.shiftLeft (Nat.land (Nat.shiftRight c (Nat.add k 5)) 1) 1)
      (Nat.lor (Nat.shiftLeft (Nat.land (Nat.shiftRight c (Nat.add k 10)) 1) 2)
        (Nat.lor (Nat.shiftLeft (Nat.land (Nat.shiftRight c (Nat.add k 15)) 1) 3)
          (Nat.shiftLeft (Nat.land (Nat.shiftRight c (Nat.add k 20)) 1) 4))))

@[expose] def rowCK (o : Ops α) (s : Nat) (A : M5 α) (k : R5 α → α) : α :=
  o.bd (sel o s A.r0.e0 A.r1.e0 A.r2.e0 A.r3.e0 A.r4.e0) fun y0 =>
  o.bd (sel o s A.r0.e1 A.r1.e1 A.r2.e1 A.r3.e1 A.r4.e1) fun y1 =>
  o.bd (sel o s A.r0.e2 A.r1.e2 A.r2.e2 A.r3.e2 A.r4.e2) fun y2 =>
  o.bd (sel o s A.r0.e3 A.r1.e3 A.r2.e3 A.r3.e3 A.r4.e3) fun y3 =>
  o.bd (sel o s A.r0.e4 A.r1.e4 A.r2.e4 A.r3.e4 A.r4.e4) fun y4 =>
  k ⟨y0, y1, y2, y3, y4⟩

@[expose] def mulCK (o : Ops α) (A : M5 α) (K : Nat) (k : M5 α → α) : α :=
  rowCK o (rowN K 0) A fun r0 => rowCK o (rowN K 1) A fun r1 => rowCK o (rowN K 2) A fun r2 =>
  rowCK o (rowN K 3) A fun r3 => rowCK o (rowN K 4) A fun r4 => k ⟨r0, r1, r2, r3, r4⟩

@[expose] def rowKC (o : Ops α) (K : Nat) (r : R5 α) (k : R5 α → α) : α :=
  o.bd (sel o (colN K 0) r.e0 r.e1 r.e2 r.e3 r.e4) fun y0 =>
  o.bd (sel o (colN K 1) r.e0 r.e1 r.e2 r.e3 r.e4) fun y1 =>
  o.bd (sel o (colN K 2) r.e0 r.e1 r.e2 r.e3 r.e4) fun y2 =>
  o.bd (sel o (colN K 3) r.e0 r.e1 r.e2 r.e3 r.e4) fun y3 =>
  o.bd (sel o (colN K 4) r.e0 r.e1 r.e2 r.e3 r.e4) fun y4 =>
  k ⟨y0, y1, y2, y3, y4⟩

@[expose] def mulKC (o : Ops α) (K : Nat) (A : M5 α) (k : M5 α → α) : α :=
  rowKC o K A.r0 fun r0 => rowKC o K A.r1 fun r1 => rowKC o K A.r2 fun r2 =>
  rowKC o K A.r3 fun r3 => rowKC o K A.r4 fun r4 => k ⟨r0, r1, r2, r3, r4⟩

@[expose] def neR (o : Ops α) (r s : R5 α) : α :=
  o.o (o.o (o.o (o.o (o.x r.e0 s.e0) (o.x r.e1 s.e1)) (o.x r.e2 s.e2)) (o.x r.e3 s.e3))
    (o.x r.e4 s.e4)

@[expose] def neM (o : Ops α) (A B : M5 α) : α :=
  o.o (o.o (o.o (o.o (neR o A.r0 B.r0) (neR o A.r1 B.r1)) (neR o A.r2 B.r2)) (neR o A.r3 B.r3))
    (neR o A.r4 B.r4)

@[expose] def neB (o : Ops α) (p : α) (b : Bool) : α :=
  Bool.rec (motive := fun _ => α) p (o.x p o.t) b

@[expose] def neRN (o : Ops α) (r : R5 α) (n : Nat) : α :=
  o.o (o.o (o.o (o.o (neB o r.e0 (bitB n 0)) (neB o r.e1 (bitB n 1))) (neB o r.e2 (bitB n 2)))
    (neB o r.e3 (bitB n 3))) (neB o r.e4 (bitB n 4))

@[expose] def neMN (o : Ops α) (A : M5 α) (K : Nat) : α :=
  o.o (o.o (o.o (o.o (neRN o A.r0 (rowN K 0)) (neRN o A.r1 (rowN K 1)))
    (neRN o A.r2 (rowN K 2))) (neRN o A.r3 (rowN K 3))) (neRN o A.r4 (rowN K 4))

@[expose] def bnot (o : Ops α) (p : α) : α := o.x p o.t

@[expose] def nconj (o : Ops α) (A : M5 α) (K K' : Nat) : α :=
  mulCK o A K fun L => mulKC o K' A fun R => neM o L R

@[expose] def nzv (o : Ops α) (v : Nat) (A : M5 α) : α :=
  o.o (o.o (o.o (o.o (sel o v A.r0.e0 A.r1.e0 A.r2.e0 A.r3.e0 A.r4.e0)
    (sel o v A.r0.e1 A.r1.e1 A.r2.e1 A.r3.e1 A.r4.e1))
    (sel o v A.r0.e2 A.r1.e2 A.r2.e2 A.r3.e2 A.r4.e2))
    (sel o v A.r0.e3 A.r1.e3 A.r2.e3 A.r3.e3 A.r4.e3))
    (sel o v A.r0.e4 A.r1.e4 A.r2.e4 A.r3.e4 A.r4.e4)

@[expose] def nsK (o : Ops α) (A : M5 α) : α :=
  Nat.rec (motive := fun _ => α) o.t
    (fun n acc => o.bd acc fun acc => o.a acc (nzv o (Nat.succ n) A)) 31

@[expose] def chk1 (o : Ops α) (A : M5 α) : α :=
  o.bd (nsK o A) fun ns => o.bd (nconj o A uvC uvC) fun nu => o.bd (nconj o A tC tC) fun nt =>
  mulK o A A fun A2 => mulK o A2 A2 fun A4 => mulK o A4 A4 fun A8 => mulK o A8 A8 fun A16 =>
  mulK o A16 A16 fun A32 => mulK o A32 A32 fun A64 =>
    o.o (o.o (o.o (bnot o ns) nu) nt) (bnot o (neMN o A64 idC))

@[expose] def inD (o : Ops α) (A : M5 α) (d : Nat) : α :=
  o.bd (nconj o A d 16916514) fun q0 => o.bd (nconj o A d 17043521) fun q1 =>
  o.bd (nconj o A d 18000930) fun q2 => o.bd (nconj o A d 18191425) fun q3 =>
  o.bd (nconj o A d 19114018) fun q4 => o.bd (nconj o A d 19209281) fun q5 =>
  o.bd (nconj o A d 20128802) fun q6 => o.bd (nconj o A d 20224065) fun q7 =>
  bnot o (o.a (o.a (o.a q0 q1) (o.a q2 q3)) (o.a (o.a q4 q5) (o.a q6 q7)))

@[expose] def inV (o : Ops α) (A : M5 α) (d : Nat) : α :=
  o.bd (nconj o A d 17043521) fun q0 => o.bd (nconj o A d 20224065) fun q1 =>
  o.bd (nconj o A d 18191425) fun q2 => o.bd (nconj o A d 19209281) fun q3 =>
  bnot o (o.a (o.a q0 q1) (o.a q2 q3))

@[expose] def chk2 (o : Ops α) (A : M5 α) : α :=
  o.bd (nsK o A) fun ns => o.bd (nconj o A uvC uvC) fun nu =>
  o.bd (inD o A uvC) fun d0 => o.bd (inD o A tC) fun d1 => o.bd (inD o A uC) fun d2 =>
  o.bd (inV o A uvC) fun v0 => o.bd (inV o A tC) fun v1 =>
    o.o (o.o (o.o (bnot o ns) nu) (bnot o (o.a d0 (o.a d1 d2)))) (o.a v0 v1)

@[expose] def natOps (t : Nat) : Ops Nat := ⟨Nat.land, Nat.lor, Nat.xor, t, 0, frcN⟩

@[expose] def nthL (L : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun a _ ih i => Nat.rec (motive := fun _ => Nat) a (fun n _ => ih n) i) L

@[expose] def nthLL (L : List (List Nat)) : Nat → List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun a _ ih i => Nat.rec (motive := fun _ => List Nat) a (fun n _ => ih n) i) L

@[expose] def allL (f : Nat → Bool) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun a _ acc => Bool.rec (motive := fun _ => Bool) false acc (f a)) L

@[expose] def codeE (e : Nat) : Nat := Nat.land e 33554431

@[expose] def tauN (c op : Nat) : Nat :=
  Nat.xor c (Nat.shiftLeft (Nat.land (Nat.shiftRight c (Nat.shiftRight op 5)) 1) (Nat.land op 31))

@[expose] def ptS (ops : List Nat) (c : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) c (fun op _ acc => tauN acc op) ops

@[expose] def tvI (Ms : List Nat) (I op : Nat) : Nat :=
  frcN (Nat.land I (nthL Ms (Nat.shiftRight op 5))) fun A =>
  frcN (Nat.land A (nthL Ms (Nat.land op 31))) fun A1 =>
    Nat.lor (Nat.xor I A) (Nat.lor (Nat.shiftRight A1 (Nat.shiftLeft 1 (Nat.land op 31)))
      (Nat.shiftLeft (Nat.xor A A1) (Nat.shiftLeft 1 (Nat.land op 31))))

@[expose] def imgS (Ms : List Nat) (I : Nat) (ops : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun I => I) (fun op _ ih I => frcN (tvI Ms I op) ih)
    ops I

@[expose] def roundS (Ms : List Nat) (Os : List (List Nat)) (U : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) U
    (fun ops _ acc => frcN acc fun acc => Nat.lor acc (imgS Ms U ops)) Os

@[expose] def roundsS (Ms : List Nat) (Os : List (List Nat)) (n U : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) U (fun _ ih => frcN ih fun V => roundS Ms Os V) n

@[expose] def opOK (op : Nat) : Bool :=
  Nat.blt (Nat.land op 31) 21 && Nat.blt (Nat.shiftRight op 5) 21 &&
    !Nat.beq (Nat.land op 31) (Nat.shiftRight op 5)

open CFSG.CGT.Stroth77.GL5 (r0 r1 r2 r3 r4 ofRows vCodes) in
@[expose] def vmF (v m0 m1 m2 m3 m4 : Nat) : Nat :=
  Nat.xor (Nat.xor (Nat.xor (Nat.xor (Bool.rec (motive := fun _ => Nat) 0 m0 (bitB v 0))
    (Bool.rec (motive := fun _ => Nat) 0 m1 (bitB v 1))) (Bool.rec (motive := fun _ => Nat) 0 m2 (bitB v 2)))
    (Bool.rec (motive := fun _ => Nat) 0 m3 (bitB v 3))) (Bool.rec (motive := fun _ => Nat) 0 m4 (bitB v 4))

open CFSG.CGT.Stroth77.GL5 (r0 r1 r2 r3 r4 ofRows) in
@[expose] def mulF (a b : Nat) : Nat :=
  ofRows (vmF (r0 b) (r0 a) (r1 a) (r2 a) (r3 a) (r4 a)) (vmF (r1 b) (r0 a) (r1 a) (r2 a) (r3 a) (r4 a))
    (vmF (r2 b) (r0 a) (r1 a) (r2 a) (r3 a) (r4 a)) (vmF (r3 b) (r0 a) (r1 a) (r2 a) (r3 a) (r4 a))
    (vmF (r4 b) (r0 a) (r1 a) (r2 a) (r3 a) (r4 a))

@[expose] def powF (h : Nat) (k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) idC (fun _ acc => mulF h acc) k

open CFSG.CGT.Stroth77.GL5 (vCodes) in
@[expose] def goodF (h : Nat) : Bool :=
  mulF h uvC == mulF uvC h && mulF h tC == mulF tC h && !vCodes.contains h

@[expose] def kUT : List Nat := [1024, 2048, 32768, 65536, 1048576, 2097152, 17043521]

@[expose] def pivUT : List Nat := [10, 11, 15, 16, 20, 21, 24]

@[expose] def comboUT (p : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun j acc => Bool.rec (motive := fun _ => Nat) acc (Nat.xor acc (nthL kUT j)) (bitB p j)) 7

@[expose] def gathUT (c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun j acc => Bool.rec (motive := fun _ => Nat) acc (Nat.add acc (Nat.shiftLeft 1 j))
      (bitB c (nthL pivUT j))) 7

open CFSG.CGT.Stroth77.GL5 (vCodes) in
@[expose] def goodUT (h : Nat) : Bool := Nat.beq (comboUT (gathUT h)) h && !vCodes.contains h

@[expose] def cenUTP (p : Nat) : Bool :=
  mulF (comboUT p) uvC == mulF uvC (comboUT p) && mulF (comboUT p) tC == mulF tC (comboUT p)

@[expose] def cenUTOK : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun p acc => Bool.rec (motive := fun _ => Bool) false (cenUTP p) acc) 128

@[expose] def mtUT (r b j : Nat) : Nat :=
  Nat.land (Nat.mul (Nat.land (Nat.shiftRight b j) 1082401) 31) (Nat.mul r 1082401)

open CFSG.CGT.Stroth77.GL5 (r0 r1 r2 r3 r4) in
@[expose] def mulUT (a b : Nat) : Nat :=
  Nat.xor (Nat.xor (Nat.xor (Nat.xor (mtUT (r0 a) b 0) (mtUT (r1 a) b 1)) (mtUT (r2 a) b 2))
    (mtUT (r3 a) b 3)) (mtUT (r4 a) b 4)

@[expose] def powUT (h : Nat) (k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) h (fun _ acc => mulUT h acc) k

@[expose] def certOK (X : List Nat) (e : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) false
    (goodUT (mulUT (nthL X (Nat.shiftRight e 46))
      (powUT (mulUT (nthL X (Nat.land (Nat.shiftRight e 36) 31))
        (powUT (mulUT (nthL X (Nat.land (Nat.shiftRight e 25) 31)) (codeE e))
          (Nat.pred (Nat.land (Nat.shiftRight e 30) 63))))
        (Nat.pred (Nat.land (Nat.shiftRight e 41) 31)))))
    (Nat.blt (Nat.shiftRight e 46) 24 && Nat.blt (Nat.land (Nat.shiftRight e 36) 31) 24 &&
      Nat.blt (Nat.land (Nat.shiftRight e 25) 31) 24)

@[expose] def certsOK (X : List Nat) (B : List (List Nat)) : Bool :=
  cenUTOK && List.rec (motive := fun _ => Bool) true
    (fun l _ acc => Bool.rec (motive := fun _ => Bool) false acc (allL (certOK X) l)) B

@[expose] def x0OK (X : List Nat) : Bool := X == x0Words.toList.map evalList

@[expose] def rwL (l p i : Nat) : Nat :=
  Nat.lor (Nat.land (Nat.shiftRight p (Nat.mul 4 i)) 15)
    (Bool.rec (motive := fun _ => Nat) 0 16 (bitB p 20 && bitB l i))

open CFSG.CGT.Stroth77.GL5 (ofRows) in
@[expose] def expW (l p : Nat) : Nat :=
  ofRows (rwL l p 0) (rwL l p 1) (rwL l p 2) (rwL l p 3) (rwL l p 4)

@[expose] def repL : List Nat := [1, 4, 6, 20]

@[expose] def basisW (ops : List Nat) (l g : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun b acc => Bool.rec (motive := fun _ => Bool) false acc
      (Nat.beq (expW l (ptS ops (Nat.shiftLeft 1 b))) (mulC g (expW l (Nat.shiftLeft 1 b))))) 21

@[expose] def gensW (LW : List (List Nat)) (cl : Nat) : List (List Nat) :=
  [nthLL LW (Nat.mul 4 cl), nthLL LW (Nat.add (Nat.mul 4 cl) 1), nthLL LW (Nat.add (Nat.mul 4 cl) 2),
    nthLL LW (Nat.add (Nat.mul 4 cl) 3)]

@[expose] def lwOK (LW : List (List Nat)) (cl l : Nat) : Bool :=
  allL opOK (nthLL LW (Nat.mul 4 cl)) && allL opOK (nthLL LW (Nat.add (Nat.mul 4 cl) 1)) &&
  allL opOK (nthLL LW (Nat.add (Nat.mul 4 cl) 2)) && allL opOK (nthLL LW (Nat.add (Nat.mul 4 cl) 3)) &&
  basisW (nthLL LW (Nat.mul 4 cl)) l uvC && basisW (nthLL LW (Nat.add (Nat.mul 4 cl) 1)) l tC &&
  basisW (nthLL LW (Nat.add (Nat.mul 4 cl) 2)) l uC && basisW (nthLL LW (Nat.add (Nat.mul 4 cl) 3)) l rhoC

@[expose] def seedOK (X : List Nat) (B : List (List Nat)) (l j d : Nat) : Bool :=
  Nat.blt (Nat.land (Nat.shiftRight d 10) 31) 24 &&
  Nat.beq (expW l (Nat.add 1048576 (Nat.add (Nat.mul 1024 j) (Nat.land d 1023))))
    (mulUT (codeE (nthL (nthLL B (Nat.shiftRight d 27)) (Nat.land (Nat.shiftRight d 15) 4095)))
      (nthL X (Nat.land (Nat.shiftRight d 10) 31)))

@[expose] def seedsOK (X : List Nat) (B : List (List Nat)) (l : Nat) (S : List (List Nat))
    (j0 : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun s _ ih j => Bool.rec (motive := fun _ => Bool) false (ih (Nat.succ j))
      (allL (seedOK X B l j) s)) S j0

@[expose] def leafS (s : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun d _ acc => Nat.lor acc (Nat.shiftLeft 1 (Nat.land d 1023))) s

@[expose] def indS (S : List (List Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun s _ acc => frcN acc fun acc => Nat.lor (Nat.shiftLeft acc 1024) (leafS s)) S

@[expose] def msW (k : List Nat → Bool) : Bool :=
  frc (pln 0 21) fun m0 => frc (pln 1 21) fun m1 => frc (pln 2 21) fun m2 =>
  frc (pln 3 21) fun m3 => frc (pln 4 21) fun m4 => frc (pln 5 21) fun m5 =>
  frc (pln 6 21) fun m6 => frc (pln 7 21) fun m7 => frc (pln 8 21) fun m8 =>
  frc (pln 9 21) fun m9 => frc (pln 10 21) fun m10 => frc (pln 11 21) fun m11 =>
  frc (pln 12 21) fun m12 => frc (pln 13 21) fun m13 => frc (pln 14 21) fun m14 =>
  frc (pln 15 21) fun m15 => frc (pln 16 21) fun m16 => frc (pln 17 21) fun m17 =>
  frc (pln 18 21) fun m18 => frc (pln 19 21) fun m19 => frc (pln 20 21) fun m20 =>
    k [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19,
      m20]

@[expose] def rowW (Ms : List Nat) (l i : Nat) : R5 Nat :=
  ⟨nthL Ms (Nat.mul 4 i), nthL Ms (Nat.add (Nat.mul 4 i) 1), nthL Ms (Nat.add (Nat.mul 4 i) 2),
    nthL Ms (Nat.add (Nat.mul 4 i) 3), Bool.rec (motive := fun _ => Nat) 0 (nthL Ms 20) (bitB l i)⟩

@[expose] def matW (Ms : List Nat) (l : Nat) : M5 Nat :=
  ⟨rowW Ms l 0, rowW Ms l 1, rowW Ms l 2, rowW Ms l 3, rowW Ms l 4⟩

@[expose] def covW (X : List Nat) (B LW : List (List Nat)) (cl l : Nat) (S : List (List Nat)) :
    Bool :=
  lwOK LW cl l && seedsOK X B l S 0 &&
  (frc (Nat.sub (Nat.shiftLeft 1 2097152) 1) fun t => msW fun Ms =>
    frc (Nat.shiftLeft (indS S) 1048576) fun U0 => frc (roundsS Ms (gensW LW cl) 3 U0) fun U =>
      Nat.beq (Nat.land (nsK (natOps t) (matW Ms l)) (Nat.xor U t)) 0)

@[expose] def anyN (f : Nat → Bool) (n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun i acc => Bool.rec (motive := fun _ => Bool) (f i) true acc) n

@[expose] def redOK (X : List Nat) : Bool :=
  allL (fun y => nonsing y && Nat.beq (powF y 24) idC) X &&
  Nat.rec (motive := fun _ => Bool) true (fun m acc => Bool.rec (motive := fun _ => Bool) false
    (Nat.beq (Nat.land m 15) 0 || anyN (fun i =>
      Nat.beq (colN (mulC (expW m 1048576) (nthL X (Nat.mod i 24))) 4) (nthL repL (Nat.div i 24))) 96)
    acc) 32

@[expose] def kB : List Nat :=
  [1024, 2048, 28672, 32768, 65536, 135234, 270369, 536675, 1048576, 2097152, 4198464, 8396832,
    16789600]

@[expose] def pivK : List Nat := [10, 11, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]

@[expose] def comboK (p : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun j acc => Bool.rec (motive := fun _ => Nat) acc (Nat.xor acc (nthL kB j)) (bitB p j)) 13

@[expose] def gathK (c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun j acc => Bool.rec (motive := fun _ => Nat) acc (Nat.add acc (Nat.shiftLeft 1 j))
      (bitB c (nthL pivK j))) 13

@[expose] def allR (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun r acc => Bool.rec (motive := fun _ => Bool) false (f r) acc) 32

@[expose] def cuvR (i x a0 a1 a2 a3 a4 : Nat) : Bool :=
  Nat.beq (vmF (rowN uvC i) a0 a1 a2 a3 a4)
    (vmF x (rowN uvC 0) (rowN uvC 1) (rowN uvC 2) (rowN uvC 3) (rowN uvC 4))

@[expose] def cuvOK : Bool :=
  open CFSG.CGT.Stroth77.GL5 (ofRows) in
  allR fun a0 => !cuvR 0 a0 a0 0 0 0 0 || allR fun a1 => !cuvR 1 a1 a0 a1 0 0 0 ||
  allR fun a2 => !cuvR 2 a2 a0 a1 a2 0 0 || allR fun a3 => !cuvR 3 a3 a0 a1 a2 a3 0 ||
  allR fun a4 => !cuvR 4 a4 a0 a1 a2 a3 a4 ||
    Nat.beq (comboK (gathK (ofRows a0 a1 a2 a3 a4))) (ofRows a0 a1 a2 a3 a4)

@[expose] noncomputable def plC (b : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun j acc => Bool.rec (motive := fun _ => Nat) acc (Nat.xor acc (pln j 13)) (bitB (nthL kB j) b))
    13

@[expose] noncomputable def rowPC (i : Nat) (k : R5 Nat → Bool) : Bool :=
  frc (plC (Nat.mul 5 i)) fun p0 => frc (plC (Nat.add (Nat.mul 5 i) 1)) fun p1 =>
  frc (plC (Nat.add (Nat.mul 5 i) 2)) fun p2 => frc (plC (Nat.add (Nat.mul 5 i) 3)) fun p3 =>
  frc (plC (Nat.add (Nat.mul 5 i) 4)) fun p4 => k ⟨p0, p1, p2, p3, p4⟩

@[expose] noncomputable def plKC (k : M5 Nat → Bool) : Bool :=
  rowPC 0 fun r0 => rowPC 1 fun r1 => rowPC 2 fun r2 => rowPC 3 fun r3 => rowPC 4 fun r4 =>
    k ⟨r0, r1, r2, r3, r4⟩

@[expose] noncomputable def sliceC (f : Ops Nat → M5 Nat → Nat) : Bool :=
  frc (Nat.sub (Nat.pow 2 (Nat.pow 2 13)) 1) fun t => plKC fun P => Nat.beq (f (natOps t) P) t

end CFSG.KC.GL5B

end
