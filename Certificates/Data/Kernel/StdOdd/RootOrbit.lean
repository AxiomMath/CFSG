module

public section

namespace CFSG.KC.StdOdd.Orbit

@[expose] noncomputable def andB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) false b a

@[expose] noncomputable def notB (b : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) true false b

@[expose] noncomputable def forceN (y : Nat) (k : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (k (nat_lit 0)) (fun m _ => k (Nat.succ m)) y

@[expose] noncomputable def nthN (l : List Nat) (i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun x _ ih i => Nat.rec (motive := fun _ => Nat) x (fun j _ => ih j) i) l i

@[expose] noncomputable def lenN (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) l

@[expose] noncomputable def full (n : Nat) : Nat :=
  Nat.sub (Nat.shiftLeft (nat_lit 1) n) (nat_lit 1)

@[expose] noncomputable def rowX (r : Nat) (PL : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun P _ ih r acc => Bool.rec (motive := fun _ => Nat)
      (ih (Nat.shiftRight r (nat_lit 1)) (Nat.xor acc P))
      (ih (Nat.shiftRight r (nat_lit 1)) acc)
      (Nat.beq (Nat.land r (nat_lit 1)) (nat_lit 0))) PL r (nat_lit 0)

@[expose] noncomputable def dsw (d m x : Nat) : Nat :=
  forceN (Nat.land (Nat.xor (Nat.shiftRight x d) x) m) fun t =>
    Nat.xor x (Nat.xor t (Nat.shiftLeft t d))

@[expose] noncomputable def net (Ds Ms : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => List Nat → Nat → Nat) (fun _ x => x)
    (fun m _ ih Ds x => List.rec (motive := fun _ => Nat) x
      (fun d Ds' _ => forceN (dsw d m x) (ih Ds')) Ds)
    Ms Ds x

@[expose] noncomputable def netRev (Ds Ms : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => List Nat → Nat → Nat) (fun _ x => x)
    (fun m _ ih Ds x => List.rec (motive := fun _ => Nat) x
      (fun d Ds' _ => forceN (ih Ds' x) (dsw d m)) Ds)
    Ms Ds x

@[expose] noncomputable def stagesOK (Ds Ms : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
    (fun m _ ih Ds => List.rec (motive := fun _ => Bool) true
      (fun d Ds' _ => andB (Nat.beq (Nat.land m (Nat.shiftLeft m d)) (nat_lit 0)) (ih Ds')) Ds)
    Ms Ds

@[expose] noncomputable def closeOK (Ds Ms : List Nat) (M : Nat) (PL : List Nat) (c : Nat) : Bool :=
  Nat.beq (net Ds Ms (rowX (Nat.shiftRight M (Nat.mul (nat_lit 156) c)) PL)) (nthN PL c)

@[expose] noncomputable def sortStep (x lt eq : Nat) (k : Nat → Nat → Nat) : Nat :=
  forceN (Nat.land eq (Nat.shiftRight x (nat_lit 1))) fun ey =>
  forceN (Nat.lor lt (Nat.sub ey (Nat.land ey x))) fun lt' =>
  forceN (Nat.land eq (Nat.xor x (Nat.shiftRight x (nat_lit 1)))) fun ed =>
  forceN (Nat.sub eq ed) fun eq' => k lt' eq'

@[expose] noncomputable def ltMask (PL : List Nat) (n : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun lt _ => lt)
    (fun x _ ih lt eq => sortStep x lt eq ih) PL (nat_lit 0) (full (Nat.sub n (nat_lit 1)))

@[expose] noncomputable def sigPlanes (PL : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat → Bool → List Nat)
    (fun ev od _ => List.rec (motive := fun _ => List Nat) ev (fun x _ ih => List.cons x ih) od)
    (fun x _ ih ev od par => Bool.rec (motive := fun _ => List Nat)
      (ih (List.cons x ev) od true) (ih ev (List.cons x od) false) par)
    PL List.nil List.nil false

@[expose] noncomputable def sortOK (PL : List Nat) (n : Nat) : Bool :=
  Nat.beq (ltMask (sigPlanes PL) n) (full (Nat.sub n (nat_lit 1)))

@[expose] noncomputable def colEq (PL : List Nat) (r pat : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun P _ ih pat =>
      andB (Nat.beq (Nat.land (Nat.shiftRight P r) (nat_lit 1)) (Nat.land pat (nat_lit 1)))
        (ih (Nat.shiftRight pat (nat_lit 1)))) PL pat

@[expose] noncomputable def rootOK (PL : List Nat) (r : Nat) : Bool :=
  colEq PL r (Nat.shiftLeft (nat_lit 1) (nat_lit 14))

@[expose] noncomputable def stepN (DA MA DB MB : List Nat) (X : Nat) : Nat :=
  Nat.lor (Nat.lor X (net DA MA X)) (Nat.lor (net DB MB X) (netRev DB MB X))

end CFSG.KC.StdOdd.Orbit

end
