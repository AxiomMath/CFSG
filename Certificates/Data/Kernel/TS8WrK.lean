module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8WrCheck

public section

namespace CFSG.KC.TS8WrK

@[expose] noncomputable def andB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) false b a

@[expose] noncomputable def orB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) b true a

@[expose] noncomputable def notB (a : Bool) : Bool := Bool.rec (motive := fun _ => Bool) true false a

@[expose] noncomputable def ifN (c : Bool) (t e : Nat) : Nat := Bool.rec (motive := fun _ => Nat) e t c

@[expose] noncomputable def letB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def allN (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i ih => andB (f i) ih) n

@[expose] noncomputable def allL (l : List Nat) (f : Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => andB (f x) ih) l

@[expose] noncomputable def memN (x : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun y _ ih => orB (Nat.beq x y) ih) l

@[expose] noncomputable def filterL (l : List Nat) (f : Nat → Bool) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun x _ ih =>
    Bool.rec (motive := fun _ => List Nat) ih (x :: ih) (f x)) l

@[expose] noncomputable def appL (l m : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) m (fun x _ ih => x :: ih) l

@[expose] noncomputable def lenL (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => Nat.succ ih) l

@[expose] noncomputable def tK (TB a b : Nat) : Nat :=
  Nat.mod (Nat.shiftRight TB (Nat.mul 5 (Nat.add (Nat.mul 32 a) b))) 32

@[expose] noncomputable def mulK (TB x y : Nat) : Nat :=
  ifN (Nat.beq (Nat.mod x 2) 1)
    (Nat.add (Nat.mul 64 (tK TB (Nat.div x 64) (Nat.mod (Nat.div y 2) 32)))
      (Nat.add (Nat.mul 2 (tK TB (Nat.mod (Nat.div x 2) 32) (Nat.div y 64)))
        (Nat.sub 1 (Nat.mod y 2))))
    (Nat.add (Nat.mul 64 (tK TB (Nat.div x 64) (Nat.div y 64)))
      (Nat.add (Nat.mul 2 (tK TB (Nat.mod (Nat.div x 2) 32) (Nat.mod (Nat.div y 2) 32)))
        (Nat.mod y 2)))

@[expose] noncomputable def tbOK (TB one : Nat) : Bool :=
  andB (allN 32 fun a => allN 32 fun b =>
      Nat.beq (tK TB a b) (CFSG.EvenSporadicStandard.Fin76b.TS8Wr.t0 a b))
    (Nat.beq one (Nat.mul 66 CFSG.EvenSporadicStandard.Fin76b.TS8Wr.i0))

@[expose] noncomputable def rootsOf (RT : List (Nat × List Nat)) (s : Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun p _ ih =>
    Bool.rec (motive := fun _ => List Nat) ih p.2 (Nat.beq p.1 s)) RT

@[expose] noncomputable def rootsGo (TB s : Nat) (l : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true) (fun r _ ih lo =>
    andB (Nat.ble lo r) (andB (Nat.blt r 2048) (andB (Nat.beq (mulK TB r r) s)
      (ih (Nat.succ r))))) l

@[expose] noncomputable def rtGo (TB : Nat) (RT : List (Nat × List Nat)) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true) (fun p _ ih lo =>
    andB (Nat.ble lo p.1) (andB (rootsGo TB p.1 p.2 0) (ih (Nat.succ p.1)))) RT

@[expose] noncomputable def sumLen (RT : List (Nat × List Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun p _ ih => Nat.add (lenL p.2) ih) RT

@[expose] noncomputable def rtOK (TB : Nat) (RT : List (Nat × List Nat)) : Bool :=
  andB (Nat.beq (sumLen RT) 2048) (rtGo TB RT 0)

@[expose] noncomputable def memKey (x : Nat) (ZA : List (Nat × List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun p _ ih => orB (Nat.beq x p.1) ih) ZA

@[expose] noncomputable def zRec (TB one : Nat) (ZA : List (Nat × List Nat)) (x : Nat)
    (p : Nat × Nat) : Bool :=
  orB (Nat.beq x one) (andB (memKey p.1 ZA) (andB (Nat.blt p.2 2048)
    (Nat.beq (mulK TB p.2 x) (mulK TB p.1 p.2))))

@[expose] noncomputable def zGo (TB one : Nat) (ZA : List (Nat × List Nat)) (xs : List Nat) :
    List (Nat × Nat) → Bool :=
  List.rec (motive := fun _ => List (Nat × Nat) → Bool) (fun _ => true) (fun x _ ih zc =>
    List.rec (motive := fun _ => Bool) false (fun p tl _ => andB (zRec TB one ZA x p) (ih tl)) zc)
    xs

@[expose] noncomputable def zOK (TB : Nat) (RT : List (Nat × List Nat)) (one : Nat)
    (ZA : List (Nat × List Nat)) (ZC : List (Nat × Nat)) : Bool :=
  zGo TB one ZA (rootsOf RT one) ZC

@[expose] noncomputable def aCand (TB one z a : Nat) : Bool :=
  letB (mulK TB a z) fun az => letB (mulK TB az az) fun t =>
    andB (notB (Nat.beq t one)) (andB (notB (Nat.beq t a)) (andB (Nat.beq (mulK TB t t) one)
      (andB (Nat.beq (mulK TB a t) (mulK TB t a)) (Nat.beq (mulK TB z t) (mulK TB t z)))))

@[expose] noncomputable def aRec (TB z : Nat) (al : List Nat) (a : Nat) (p : Nat × Nat) : Bool :=
  andB (memN p.1 al) (andB (Nat.blt p.2 2048) (andB (Nat.beq (mulK TB p.2 z) (mulK TB z p.2))
    (Nat.beq (mulK TB p.2 a) (mulK TB p.1 p.2))))

@[expose] noncomputable def aGo (TB z : Nat) (al : List Nat) (xs : List Nat) :
    List (Nat × Nat) → Bool :=
  List.rec (motive := fun _ => List (Nat × Nat) → Bool) (fun _ => true) (fun x _ ih ac =>
    List.rec (motive := fun _ => Bool) false (fun p tl _ => andB (aRec TB z al x p) (ih tl)) ac)
    xs

@[expose] noncomputable def zaGo (TB : Nat) (RT : List (Nat × List Nat)) (one : Nat)
    (ZA : List (Nat × List Nat)) : List (List (Nat × Nat)) → Bool :=
  List.rec (motive := fun _ => List (List (Nat × Nat)) → Bool) (fun _ => true) (fun p _ ih AC =>
    List.rec (motive := fun _ => Bool) false (fun acl tl _ =>
      andB (Nat.blt p.1 2048) (andB (allL p.2 fun r => Nat.blt r 2048)
        (andB (aGo TB p.1 p.2 (filterL (rootsOf RT one) (aCand TB one p.1)) acl) (ih tl)))) AC)
    ZA

@[expose] noncomputable def flatZA (ZA : List (Nat × List Nat)) : List (Nat × Nat) :=
  List.rec (motive := fun _ => List (Nat × Nat)) [] (fun p _ ih =>
    List.rec (motive := fun _ => List (Nat × Nat)) ih (fun a _ ih' => (p.1, a) :: ih') p.2) ZA

@[expose] noncomputable def lenP (l : List (Nat × Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => Nat.succ ih) l

@[expose] noncomputable def zaOK (TB : Nat) (RT : List (Nat × List Nat)) (one : Nat)
    (ZA : List (Nat × List Nat)) (AC : List (List (Nat × Nat))) (n : Nat) : Bool :=
  andB (Nat.beq (lenP (flatZA ZA)) n) (zaGo TB RT one ZA AC)

@[expose] noncomputable def canon (TB a t at' g : Nat) : Bool :=
  andB (Nat.blt g (mulK TB g a)) (andB (Nat.blt g (mulK TB g t)) (Nat.blt g (mulK TB g at')))

@[expose] noncomputable def dOK (TB z a t c : Nat) : Bool :=
  andB (Nat.beq (mulK TB c a) (mulK TB a c)) (andB (Nat.beq (mulK TB c t) (mulK TB t c))
    (letB (mulK TB (mulK TB z c) z) fun h => Nat.beq (mulK TB c h) (mulK TB h c)))

@[expose] noncomputable def pairsOK (TB z t at' : Nat) (R : List Nat) : Bool :=
  allL R fun g₁ => allL R fun g₂ =>
    notB (andB (Nat.beq (mulK TB g₁ g₂) (mulK TB at' (mulK TB g₂ g₁)))
      (letB (mulK TB (mulK TB z g₂) z) fun h₂ =>
        Nat.beq (mulK TB g₁ h₂) (mulK TB t (mulK TB h₂ g₁))))

@[expose] noncomputable def rowOK (TB : Nat) (RT : List (Nat × List Nat)) (one z a : Nat) : Bool :=
  letB (mulK TB a z) fun az => letB (mulK TB az az) fun t => letB (mulK TB a t) fun at' =>
    pairsOK TB z t at' (filterL (appL (rootsOf RT one) (rootsOf RT t)) fun c =>
      andB (canon TB a t at' c) (dOK TB z a t c))

@[expose] noncomputable def nthP (l : List (Nat × Nat)) : Nat → Nat × Nat :=
  List.rec (motive := fun _ => Nat → Nat × Nat) (fun _ => (0, 0)) (fun p _ ih i =>
    Nat.rec (motive := fun _ => Nat × Nat) p (fun j _ => ih j) i) l

@[expose] noncomputable def rowChk (TB : Nat) (RT : List (Nat × List Nat)) (one : Nat)
    (ZA : List (Nat × List Nat)) (i z a : Nat) : Bool :=
  andB (andB (Nat.beq (nthP (flatZA ZA) i).1 z) (Nat.beq (nthP (flatZA ZA) i).2 a))
    (rowOK TB RT one z a)

end CFSG.KC.TS8WrK
