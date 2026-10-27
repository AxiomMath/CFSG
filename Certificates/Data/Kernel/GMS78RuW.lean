module

public import CFSG.Certificates.Kernel.Orders.Cert

public section

namespace CFSG.KC.GMSW

open CFSG.KC.Ord

@[expose] noncomputable def badLet : Nat × Bool := (nat_lit 1000, true)

@[expose] noncomputable def appK (u v : List (Nat × Bool)) : List (Nat × Bool) :=
  List.rec (motive := fun _ => List (Nat × Bool)) v (fun x _ ih => List.cons x ih) u

@[expose] noncomputable def imgLetK (z : Int) : Nat × Bool :=
  Int.rec (motive := fun _ => Nat × Bool)
    (fun n => Bool.rec (motive := fun _ => Nat × Bool) badLet
      (Nat.div n (nat_lit 2), Nat.beq (Nat.mod n (nat_lit 2)) (nat_lit 0)) (Nat.blt n (nat_lit 4)))
    (fun _ => badLet) z

@[expose] noncomputable def imgWordK (w : List Int) : List (Nat × Bool) :=
  List.rec (motive := fun _ => List (Nat × Bool)) [] (fun z _ ih => List.cons (imgLetK z) ih) w

@[expose] noncomputable def mkImgK (ws : List (List Int)) : Nat → List (List (Nat × Bool)) :=
  List.rec (motive := fun _ => Nat → List (List (Nat × Bool))) (fun _ => [])
    (fun w _ ih k => List.cons (List.cons (Nat.add k (nat_lit 2), false) (imgWordK w))
      (ih (Nat.succ k))) ws

@[expose] noncomputable def codeLetK (c : Nat) : Nat × Bool :=
  Bool.rec (motive := fun _ => Nat × Bool) badLet
    (Nat.add (Nat.div c (nat_lit 2)) (nat_lit 2), Nat.beq (Nat.mod c (nat_lit 2)) (nat_lit 0))
    (Nat.blt c (nat_lit 14))

@[expose] noncomputable def codeWordK (w : List Nat) : List (Nat × Bool) :=
  List.rec (motive := fun _ => List (Nat × Bool)) [] (fun c _ ih => List.cons (codeLetK c) ih) w

@[expose] noncomputable def mkCodesK (rs : List (List Nat)) : List (List (Nat × Bool)) :=
  List.rec (motive := fun _ => List (List (Nat × Bool))) [] (fun r _ ih => List.cons (codeWordK r) ih)
    rs

@[expose] noncomputable def natLetK (l : Nat × Bool) : Nat × Bool :=
  Prod.rec (motive := fun _ => Nat × Bool) (fun k s => Bool.rec (motive := fun _ => Nat × Bool) badLet
    (Nat.add k (nat_lit 2), s) (Nat.blt k (nat_lit 7))) l

@[expose] noncomputable def natWordK (w : List (Nat × Bool)) : List (Nat × Bool) :=
  List.rec (motive := fun _ => List (Nat × Bool)) [] (fun l _ ih => List.cons (natLetK l) ih) w

@[expose] noncomputable def mkNatK (rs : List (List (Nat × Bool))) : List (List (Nat × Bool)) :=
  List.rec (motive := fun _ => List (List (Nat × Bool))) [] (fun r _ ih => List.cons (natWordK r) ih)
    rs

@[expose] noncomputable def sgnLetK (z : Int) : Nat × Bool :=
  Int.rec (motive := fun _ => Nat × Bool)
    (fun n => Bool.rec (motive := fun _ => Nat × Bool) badLet (Nat.succ n, true)
      (andB (Nat.blt (nat_lit 0) n) (Nat.blt n (nat_lit 8))))
    (fun n => Bool.rec (motive := fun _ => Nat × Bool) badLet (Nat.add n (nat_lit 2), false)
      (Nat.blt n (nat_lit 7))) z

@[expose] noncomputable def sgnWordK (w : List Int) : List (Nat × Bool) :=
  List.rec (motive := fun _ => List (Nat × Bool)) [] (fun z _ ih => List.cons (sgnLetK z) ih) w

@[expose] noncomputable def mkSurjK (ws : List (List Int)) : Nat → List (List (Nat × Bool)) :=
  List.rec (motive := fun _ => Nat → List (List (Nat × Bool))) (fun _ => [])
    (fun w _ ih k => List.cons (appK (sgnWordK w) [(k, false)]) (ih (Nat.succ k))) ws

@[expose] noncomputable def finLetK (l : Fin 7 × Bool) : Nat × Bool :=
  Prod.rec (motive := fun _ => Nat × Bool) (fun i s => (Nat.add (Fin.val i) (nat_lit 2), s)) l

@[expose] noncomputable def finWordK (w : List (Fin 7 × Bool)) : List (Nat × Bool) :=
  List.rec (motive := fun _ => List (Nat × Bool)) [] (fun l _ ih => List.cons (finLetK l) ih) w

@[expose] noncomputable def finInvK (w : List (Fin 7 × Bool)) : List (Nat × Bool) → List (Nat × Bool) :=
  List.rec (motive := fun _ => List (Nat × Bool) → List (Nat × Bool)) (fun acc => acc)
    (fun l _ ih acc => ih (List.cons (Prod.rec (motive := fun _ => Nat × Bool)
      (fun g s => (g, notB s)) (finLetK l)) acc)) w

@[expose] noncomputable def pairRelK (p : List (Fin 7 × Bool) × List (Fin 7 × Bool)) :
    List (Nat × Bool) :=
  Prod.rec (motive := fun _ => List (Nat × Bool)) (fun u v => appK (finWordK u) (finInvK v [])) p

@[expose] noncomputable def consNe (r : List (Nat × Bool)) (rs : List (List (Nat × Bool))) :
    List (List (Nat × Bool)) :=
  List.rec (motive := fun _ => List (List (Nat × Bool))) rs (fun _ _ _ => List.cons r rs) r

@[expose] noncomputable def mkPairsK (P : List (List (Fin 7 × Bool) × List (Fin 7 × Bool))) :
    List (List (Nat × Bool)) :=
  List.rec (motive := fun _ => List (List (Nat × Bool))) [] (fun p _ ih => consNe (pairRelK p) ih) P

@[expose] noncomputable def mkPairsAllK (P : List (List (Fin 7 × Bool) × List (Fin 7 × Bool))) :
    List (List (Nat × Bool)) :=
  List.rec (motive := fun _ => List (List (Nat × Bool))) [] (fun p _ ih => List.cons (pairRelK p) ih) P

@[expose] noncomputable def relNeOK (RB : Nat → Nat) (mul : Nat → Nat → Nat)
    (rels : List (List (Nat × Bool))) (L ONE r : Nat) : Bool :=
  (fun l => andB (Nat.blt r (lenL rels))
    (notB (Nat.beq (segProd RB mul ONE L (nat_lit 0) (lenL l) l (nat_lit 0) ONE) ONE)))
  (nthRel rels r)

@[expose] noncomputable def relsNeAll (RB : Nat → Nat) (mul : Nat → Nat → Nat)
    (rels : List (List (Nat × Bool))) (L ONE lo k : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun i ih => andB ih (relNeOK RB mul rels L ONE (Nat.add lo i))) k

@[expose] noncomputable def packK (R : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun x _ ih i => Nat.lor (Nat.shiftLeft x (Nat.mul (nat_lit 6) i)) (ih (Nat.succ i))) R

@[expose] noncomputable def allLtK (R : List Nat) (n : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => andB (Nat.blt x n) ih) R

@[expose] noncomputable def xorBitsK (P i : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun j acc => Bool.rec (motive := fun _ => Nat) acc
      (Nat.xor acc (bitsN P (Nat.mul (nat_lit 6) (Nat.shiftLeft (nat_lit 1) j)) (nat_lit 6)))
      (Nat.beq (Nat.land (Nat.shiftRight i j) (nat_lit 1)) (nat_lit 1))) (nat_lit 6)

@[expose] noncomputable def rowLinK (R : List Nat) : Bool :=
  andB (Nat.beq (lenL R) (nat_lit 64)) (andB (allLtK R (nat_lit 64))
    ((fun P => Nat.rec (motive := fun _ => Bool) true
      (fun i ih => andB ih (Nat.beq (bitsN P (Nat.mul (nat_lit 6) i) (nat_lit 6)) (xorBitsK P i)))
      (nat_lit 64)) (packK R (nat_lit 0))))

@[expose] noncomputable def linTabK (T : List (List Nat)) : Bool :=
  andB (Nat.beq (lenL T) (nat_lit 6)) (List.rec (motive := fun _ => Bool) true
    (fun R _ ih => andB (rowLinK R) ih) T)

@[expose] noncomputable def mkNeK (ws : List (List (Fin 7 × Bool))) : Nat → List (List (Nat × Bool)) :=
  List.rec (motive := fun _ => Nat → List (List (Nat × Bool))) (fun _ => [])
    (fun w _ ih k => List.cons (appK (finWordK w) [(k, false)]) (ih (Nat.succ k))) ws

@[expose] noncomputable def relsEqK (a : List (List (Nat × Bool))) : List (List (Nat × Bool)) → Bool :=
  List.rec (motive := fun _ => List (List (Nat × Bool)) → Bool)
    (fun b => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) b)
    (fun u _ ih b => List.rec (motive := fun _ => Bool) false (fun v vs _ => andB (wordEq u v) (ih vs)) b)
    a

@[expose] noncomputable def relsAll (RB : Nat → Nat) (mul : Nat → Nat → Nat)
    (rels : List (List (Nat × Bool))) (L ONE lo k : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i ih => andB ih (relOK RB mul rels L ONE (Nat.add lo i))) k

end CFSG.KC.GMSW

end
