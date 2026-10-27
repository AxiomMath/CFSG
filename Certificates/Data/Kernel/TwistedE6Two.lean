module

public import Certificates.Data.Kernel.Misc.E6Std

public section

namespace CFSG.KC.TwistedE6Two

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc CFSG.KC.Misc.E6Std

@[expose] noncomputable def genK (codes bits k r : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (mulB (rootB codes bits (Nat.add k 6) 1 0) (rootB codes bits (Nat.add r 6) 1 0))
    (rootB codes bits (Nat.add k 6) 1 0) (Nat.beq r k)

@[expose] noncomputable def genWK (codes bits k r : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (mulB (rootB codes bits (Nat.add k 6) 0 1) (rootB codes bits (Nat.add r 6) 1 1))
    (rootB codes bits (Nat.add k 6) 1 0) (Nat.beq r k)

@[expose] noncomputable def gensOK (codes bits : Nat) (rho V : List Nat) (o : Nat) : Bool :=
  allN 72 fun k => andB (Nat.blt (nthV rho k) 72)
    (Nat.beq (genK codes bits k (nthV rho k)) (nthV V (Nat.add o k)))

@[expose] noncomputable def gensWOK (codes bits : Nat) (rho V : List Nat) (o : Nat) : Bool :=
  allN 72 fun k => andB (Nat.blt (nthV rho k) 72)
    (Nat.beq (genWK codes bits k (nthV rho k)) (nthV V (Nat.add o k)))

@[expose] noncomputable def oddK (V : List Nat) (T n i m : Nat) : Bool :=
  andB (Nat.beq (Nat.mod m 2) 1) (andB (Nat.blt i n) (letB (nthV V i) fun P =>
    andB (Nat.beq (powB P m) oneB) (Nat.beq (mulB P T) (mulB T P))))

@[expose] noncomputable def allLt (l : List Nat) (n : Nat) : Bool := allL l fun i => Nat.blt i n

@[expose] noncomputable def factorK (V : List Nat) (t n g : Nat) (D : List (Nat × List (Nat × Nat))) :
    Bool :=
  letB (nthV V t) fun T => D.all fun p =>
    (p.2.all fun q => oddK V T n q.1 q.2) && allLt (p.2.map Prod.fst) n && Nat.blt p.1 g &&
      Nat.beq (lineB V (p.2.map Prod.fst)) (nthV V p.1)

@[expose] noncomputable def conjB (V a : List Nat) (l : List (Nat × Nat)) : Nat :=
  l.foldl (fun acc q => mulB acc (mulB (mulB (nthV V q.1) (lineB V a))
    (powB (nthV V q.1) (Nat.sub q.2 1)))) oneB

@[expose] noncomputable def conjK (V : List Nat) (t n g : Nat) (D : List (List Nat × List (Nat × Nat))) :
    Bool :=
  letB (nthV V t) fun T => D.all fun p =>
    (p.2.all fun q => oddK V T n q.1 q.2) && allLt p.1 g && Nat.beq T (conjB V p.1 p.2)

@[expose] noncomputable def pairK (V : List Nat) (S : Nat) (w : List (Nat × Nat)) (P : Nat) :
    Bool :=
  letB P fun P => !(w.all fun q => Nat.beq (mulB (nthV V q.1) P) (mulB P (nthV V q.1))) ||
    Nat.beq P oneB || Nat.beq P S

@[expose] noncomputable def candUK (codes bits : Nat) (a0 a1 c : Bool) : Nat :=
  mulB (mulB (rootB codes bits 68 a0.toNat a1.toNat) (rootB codes bits 67 (a0 ^^ a1).toNat a1.toNat))
    (rootB codes bits 76 c.toNat 0)

@[expose] noncomputable def candVK (codes bits : Nat) (a0 a1 c1 c2 c3 : Bool) : Nat :=
  mulB (mulB (mulB (mulB (rootB codes bits 58 a0.toNat a1.toNat)
    (rootB codes bits 54 (a0 ^^ a1).toNat a1.toNat)) (rootB codes bits 72 c1.toNat 0))
    (rootB codes bits 74 c2.toNat 0)) (rootB codes bits 76 c3.toNat 0)

@[expose] noncomputable def pairUK (codes bits : Nat) (V : List Nat) (S n : Nat)
    (w : List (Nat × Nat)) (bs : List Bool) : Bool :=
  letB S fun S => (w.all fun q => oddK V S n q.1 q.2) &&
    bs.all fun a0 => bs.all fun a1 => bs.all fun c => pairK V S w (candUK codes bits a0 a1 c)

@[expose] noncomputable def pairVK (codes bits : Nat) (V : List Nat) (S n : Nat)
    (w : List (Nat × Nat)) (bs : List Bool) : Bool :=
  letB S fun S => (w.all fun q => oddK V S n q.1 q.2) &&
    bs.all fun a0 => bs.all fun a1 => bs.all fun c1 => bs.all fun c2 => bs.all fun c3 =>
      pairK V S w (candVK codes bits a0 a1 c1 c2 c3)

end CFSG.KC.TwistedE6Two

end
