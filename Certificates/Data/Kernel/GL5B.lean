module

public import Certificates.Data.Kernel.F4M3B
public import Certificates.Data.CFSGNative.Stroth15.GL5

public noncomputable section

namespace CFSG.KC.GL5B

open CFSG.KC.F4M3B (frcN frc pln)
open CFSG.CGT.Stroth77.GL5 (mulC powC good uvC tC uC rhoC idC evalList x0Words)

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

@[expose] def plS (j m s t : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) 0 t (bitB s (Nat.sub j m)))
    (pln j m) (Nat.blt j m)

@[expose] def rowP (i m s t : Nat) (k : R5 Nat → Bool) : Bool :=
  frc (plS (Nat.mul 5 i) m s t) fun p0 => frc (plS (Nat.add (Nat.mul 5 i) 1) m s t) fun p1 =>
  frc (plS (Nat.add (Nat.mul 5 i) 2) m s t) fun p2 =>
  frc (plS (Nat.add (Nat.mul 5 i) 3) m s t) fun p3 =>
  frc (plS (Nat.add (Nat.mul 5 i) 4) m s t) fun p4 => k ⟨p0, p1, p2, p3, p4⟩

@[expose] def plK (m s t : Nat) (k : M5 Nat → Bool) : Bool :=
  rowP 0 m s t fun r0 => rowP 1 m s t fun r1 => rowP 2 m s t fun r2 => rowP 3 m s t fun r3 =>
  rowP 4 m s t fun r4 => k ⟨r0, r1, r2, r3, r4⟩

@[expose] def slice (f : Ops Nat → M5 Nat → Nat) (m s : Nat) : Bool :=
  frc (Nat.sub (Nat.pow 2 (Nat.pow 2 m)) 1) fun t => plK m s t fun P => Nat.beq (f (natOps t) P) t

@[expose] def allS (f : Ops Nat → M5 Nat → Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun s acc => Bool.rec (motive := fun _ => Bool) false (slice f 20 s) acc) 32

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

@[expose] def leafB (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun e _ acc => Nat.lor acc (Nat.shiftLeft 1 (Nat.land e 32767))) l

@[expose] def indB (B : List (List Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun l _ acc => frcN acc fun acc => Nat.lor (Nat.shiftLeft acc 32768) (leafB l)) B

@[expose] def bOK (B : List (List Nat)) (i0 : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun l _ ih i => Bool.rec (motive := fun _ => Bool) false (ih (Nat.succ i))
      (allL (fun e => Nat.beq (Nat.shiftRight (codeE e) 15) i) l)) B i0

@[expose] def basisOK (ops : List Nat) (f : Nat → Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun b acc => Bool.rec (motive := fun _ => Bool) false acc
      (Nat.beq (ptS ops (Nat.shiftLeft 1 b)) (f (Nat.shiftLeft 1 b)))) 25

@[expose] def gens4 (O : List (List Nat)) : List (List Nat) :=
  [nthLL O 0, nthLL O 1, nthLL O 2, nthLL O 3]

@[expose] def opOK (op : Nat) : Bool :=
  Nat.blt (Nat.land op 31) 25 && Nat.blt (Nat.shiftRight op 5) 25 &&
    !Nat.beq (Nat.land op 31) (Nat.shiftRight op 5)

@[expose] def opsOK (RO LO : List (List Nat)) : Bool :=
  allL opOK (nthLL RO 0) && allL opOK (nthLL RO 1) && allL opOK (nthLL RO 2) &&
  allL opOK (nthLL RO 3) && allL opOK (nthLL LO 0) && allL opOK (nthLL LO 1) &&
  allL opOK (nthLL LO 2) && allL opOK (nthLL LO 3) &&
  basisOK (nthLL RO 0) (fun c => mulC c uvC) && basisOK (nthLL RO 1) (fun c => mulC c tC) &&
  basisOK (nthLL RO 2) (fun c => mulC c uC) && basisOK (nthLL RO 3) (fun c => mulC c rhoC) &&
  basisOK (nthLL LO 0) (fun c => mulC uvC c) && basisOK (nthLL LO 1) (fun c => mulC tC c) &&
  basisOK (nthLL LO 2) (fun c => mulC uC c) && basisOK (nthLL LO 3) (fun c => mulC rhoC c)

@[expose] def msK (k : List Nat → Bool) : Bool :=
  frc (pln 0 25) fun m0 => frc (pln 1 25) fun m1 => frc (pln 2 25) fun m2 =>
  frc (pln 3 25) fun m3 => frc (pln 4 25) fun m4 => frc (pln 5 25) fun m5 =>
  frc (pln 6 25) fun m6 => frc (pln 7 25) fun m7 => frc (pln 8 25) fun m8 =>
  frc (pln 9 25) fun m9 => frc (pln 10 25) fun m10 => frc (pln 11 25) fun m11 =>
  frc (pln 12 25) fun m12 => frc (pln 13 25) fun m13 => frc (pln 14 25) fun m14 =>
  frc (pln 15 25) fun m15 => frc (pln 16 25) fun m16 => frc (pln 17 25) fun m17 =>
  frc (pln 18 25) fun m18 => frc (pln 19 25) fun m19 => frc (pln 20 25) fun m20 =>
  frc (pln 21 25) fun m21 => frc (pln 22 25) fun m22 => frc (pln 23 25) fun m23 =>
  frc (pln 24 25) fun m24 =>
    k [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19,
      m20, m21, m22, m23, m24]

@[expose] def matOf (Ms : List Nat) : M5 Nat :=
  ⟨⟨nthL Ms 0, nthL Ms 1, nthL Ms 2, nthL Ms 3, nthL Ms 4⟩,
    ⟨nthL Ms 5, nthL Ms 6, nthL Ms 7, nthL Ms 8, nthL Ms 9⟩,
    ⟨nthL Ms 10, nthL Ms 11, nthL Ms 12, nthL Ms 13, nthL Ms 14⟩,
    ⟨nthL Ms 15, nthL Ms 16, nthL Ms 17, nthL Ms 18, nthL Ms 19⟩,
    ⟨nthL Ms 20, nthL Ms 21, nthL Ms 22, nthL Ms 23, nthL Ms 24⟩⟩

@[expose] def tPlane (Ms : List Nat) (t : Nat) : Nat :=
  Nat.land (nsK (natOps t) (matOf Ms))
    (Nat.lor (Nat.lor (nthL Ms 4) (nthL Ms 9)) (Nat.lor (nthL Ms 14) (nthL Ms 19)))

@[expose] def coverOK (B RO LO : List (List Nat)) : Bool :=
  bOK B 0 && opsOK RO LO &&
  (frc (Nat.sub (Nat.shiftLeft 1 33554432) 1) fun t => msK fun Ms =>
    frc (indB B) fun U0 => frc (roundsS Ms (gens4 RO) 3 U0) fun U1 =>
    frc (roundsS Ms (gens4 LO) 3 U1) fun U2 =>
      Nat.beq (Nat.land (tPlane Ms t) (Nat.xor U2 t)) 0)

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

@[expose] def certOK (X : List Nat) (e : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) false
    (goodF (mulF (nthL X (Nat.shiftRight e 46))
      (powF (mulF (nthL X (Nat.land (Nat.shiftRight e 36) 31))
        (powF (mulF (nthL X (Nat.land (Nat.shiftRight e 25) 31)) (codeE e))
          (Nat.land (Nat.shiftRight e 30) 63)))
        (Nat.land (Nat.shiftRight e 41) 31))))
    (Nat.blt (Nat.shiftRight e 46) 24 && Nat.blt (Nat.land (Nat.shiftRight e 36) 31) 24 &&
      Nat.blt (Nat.land (Nat.shiftRight e 25) 31) 24)

@[expose] def certsOK (X : List Nat) (B : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun l _ acc => Bool.rec (motive := fun _ => Bool) false acc (allL (certOK X) l)) B

@[expose] def x0OK (X : List Nat) : Bool := X == x0Words.toList.map evalList

end CFSG.KC.GL5B

end
