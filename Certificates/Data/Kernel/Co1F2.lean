module

public import Certificates.Data.Kernel.M1F2

public section

namespace CFSG.KC.Co1F2

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2

@[expose] noncomputable def getL (x : Nat) (L : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => x)
    (fun a _ ih i => Nat.rec (motive := fun _ => Nat) a (fun j _ => ih j) i) L

@[expose] noncomputable def lenL (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) L

@[expose] noncomputable def packAt (d M : Nat) (L : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun i => Nat.beq i d)
    (fun r _ ih i => strictB i fun i =>
      andB (Nat.blt r (pw2 d)) (andB (Nat.beq r (fget M i d)) (ih (Nat.succ i)))) L

@[expose] noncomputable def packB (d : Nat) (L : List Nat) (M : Nat) : Bool := packAt d M L (nat_lit 0)

@[expose] noncomputable def powK (d M e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (idF d) (fun _ acc => strictN acc fun a => mulF d a M) e

@[expose] noncomputable def lineK (d : Nat) (R : List Nat) (fac : List (Nat × Nat)) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun p _ ih acc => strictN (Prod.rec (motive := fun _ => Nat)
      (fun i e => mulF d acc (powK d (getL (idF d) R i) e)) p) ih) fac (idF d)

@[expose] noncomputable def facBelow (fac : List (Nat × Nat)) (t : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun p _ ih => andB (Prod.rec (motive := fun _ => Bool) (fun i _ => Nat.blt i t) p) ih) fac

@[expose] noncomputable def progK (d : Nat) (R : List Nat) (prog : List (List (Nat × Nat))) (t : Nat) :
    Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun t => Nat.beq (lenL R) t)
    (fun fac _ ih t => strictB t fun t =>
      andB (facBelow fac t) (andB (Nat.beq (getL (nat_lit 0) R t) (lineK d R fac)) (ih (Nat.succ t))))
    prog t

@[expose] noncomputable def invK (d M MI k : Nat) : Bool :=
  andB (Nat.blt (nat_lit 0) k) (andB (Nat.ble k (nat_lit 100000))
    (andB (Nat.beq (mulF d MI M) (idF d))
      (Nat.beq (Nat.rec (motive := fun _ => Nat)
        (M) (fun _ acc => strictN acc fun c =>
          strictN (mulF d c M) fun nx => nIf(Nat.beq nx (idF d), nat_lit 0, nx))
        (Nat.sub k (nat_lit 1))) MI)))

@[expose] noncomputable def letK (A B AI BI : Nat) (l : Nat × Bool) : Nat :=
  Prod.rec (motive := fun _ => Nat)
    (fun i s => nIf(Nat.beq i (nat_lit 0), nIf(s, A, AI), nIf(s, B, BI))) l

@[expose] noncomputable def wordK (d A B AI BI : Nat) (w : List (Nat × Bool)) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun l _ ih acc => strictN (mulF d acc (letK A B AI BI l)) ih) w (idF d)

@[expose] noncomputable def relCheckK (d A B AI BI : Nat) (rels : List (List (Nat × Bool))) : Bool :=
  andB (Nat.beq (mulF d A AI) (idF d)) (andB (Nat.beq (mulF d B BI) (idF d))
    (List.rec (motive := fun _ => Bool) true
      (fun w _ ih => andB (Nat.beq (wordK d A B AI BI w) (idF d)) ih) rels))

@[expose] noncomputable def eprodK (E : List Nat) (x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun i ih acc => strictN (nIf(bit x (Nat.sub (nat_lit 10) i),
      mulF (nat_lit 24) acc (getL (nat_lit 0) E (Nat.sub (nat_lit 10) i)), acc)) ih)
    (nat_lit 11) (idF (nat_lit 24))

@[expose] noncomputable def extK (g : Nat) (L : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun a _ ih acc => ih (List.cons (mulF (nat_lit 24) a g) acc)) L
    (List.rec (motive := fun _ => List Nat) List.nil (fun a _ ih => List.cons a ih) L)

@[expose] noncomputable def prodsK (E : List Nat) (n : Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) (List.cons (idF (nat_lit 24)) List.nil)
    (fun h ih => extK (getL (nat_lit 0) E h) ih) n

@[expose] noncomputable def countId (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun a _ ih => nIf(Nat.beq a (idF (nat_lit 24)), Nat.succ ih, ih)) L

@[expose] noncomputable def epsBasicK (E : List Nat) : Bool :=
  andB (Nat.beq (lenL E) (nat_lit 11))
    (allN (nat_lit 11) fun i => strictB (getL (nat_lit 0) E i) fun a =>
      andB (Nat.beq (mulF (nat_lit 24) a a) (idF (nat_lit 24)))
        (allN (nat_lit 11) fun j => strictB (getL (nat_lit 0) E j) fun b =>
          Nat.beq (mulF (nat_lit 24) a b) (mulF (nat_lit 24) b a)))

@[expose] noncomputable def epsInjK (E : List Nat) : Bool :=
  andB (Nat.beq (lenL E) (nat_lit 11)) (Nat.beq (countId (prodsK E (nat_lit 11))) (nat_lit 1))

@[expose] noncomputable def normK (E : List Nat) (g C : Nat) : Bool :=
  allN (nat_lit 11) fun i =>
    Nat.beq (mulF (nat_lit 24) g (getL (nat_lit 0) E i))
      (mulF (nat_lit 24) (eprodK E (fget C i (nat_lit 11))) g)

@[expose] noncomputable def orderIsK (d M n : Nat) : Bool :=
  andB (Nat.beq (powK d M n) (idF d))
    (allN n fun m => orB (Nat.beq m (nat_lit 0)) (notB (Nat.beq (powK d M m) (idF d))))

@[expose] noncomputable def trK (d X : Nat) : Nat :=
  orN d fun j => Nat.shiftLeft (orN d fun i =>
    nIf(bit X (Nat.add (Nat.mul d i) j), pw2 i, nat_lit 0)) (Nat.mul d j)

@[expose] noncomputable def vecK (d M v : Nat) : Nat := vmF d M v

@[expose] noncomputable def lowK (d v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) d
    (fun k ih => nIf(bit v (Nat.sub (Nat.sub d (nat_lit 1)) k), Nat.sub (Nat.sub d (nat_lit 1)) k, ih)) d

@[expose] noncomputable def pivK (d : Nat) (L : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun v _ ih acc => strictB (lowK d v) fun p =>
      andB (Nat.blt p d) (andB (notB (bit acc p)) (ih (Nat.lor acc (pw2 p))))) L

@[expose] noncomputable def dotK (d x y : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) false
    (fun j ih => Bool.rec (motive := fun _ => Bool) ih (notB ih)
      (andB (bit x j) (bit y j))) d

@[expose] noncomputable def qCountK (d Qt : Nat) (F : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat)
    (fun acc => Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) (dotK d acc (vecK d Qt acc)))
    (fun f _ ih acc => strictN (ih acc) fun a => strictN (ih (Nat.xor acc f)) fun b => Nat.add a b) F

@[expose] noncomputable def fixK (d Mt Qt : Nat) (F Y : List Nat) (k a b : Nat) : Bool :=
  andB (Nat.beq (lenL F) k) (andB (Nat.beq (Nat.add (lenL Y) k) d)
  (andB (Nat.beq a (pw2 k))
  (andB (List.rec (motive := fun _ => Bool) true
      (fun f _ ih => andB (Nat.blt f (pw2 d)) (andB (Nat.beq (vecK d Mt f) f) ih)) F)
  (andB (pivK d F (nat_lit 0))
  (andB (List.rec (motive := fun _ => Bool) true
      (fun y _ ih => andB (Nat.blt y (pw2 d)) ih) Y)
  (andB (pivK d (List.rec (motive := fun _ => List Nat) List.nil
      (fun y _ ih => List.cons (Nat.xor (vecK d Mt y) y) ih) Y) (nat_lit 0))
    (Nat.beq (qCountK d Qt F (nat_lit 0)) b)))))))

end CFSG.KC.Co1F2

end
