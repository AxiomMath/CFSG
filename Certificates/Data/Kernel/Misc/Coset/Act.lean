module

public import Mathlib.Init

public section

namespace CFSG.KC.MiscCoset.Act

@[expose] noncomputable def andB (a b : Bool) : Bool := Bool.rec false b a

@[expose] noncomputable def notB (a : Bool) : Bool := Bool.rec true false a

@[expose] noncomputable def allR (lo n : Nat) (p : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => andB (p (Nat.add lo k)) ih) n

@[expose] noncomputable def step (A : Nat → Nat) (L x c : Nat) : Nat := A (Nat.add (Nat.mul x L) c)

@[expose] noncomputable def walk (A : Nat → Nat) (L : Nat) (w : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun y => y) (fun c _ ih y => ih (step A L y c)) w x

@[expose] noncomputable def relsAt (A : Nat → Nat) (L : Nat) (rels : List (List Nat)) (x : Nat) :
    Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun r _ ih => andB (Nat.beq (walk A L r x) x) ih) rels

@[expose] noncomputable def pointOK (A : Nat → Nat) (m N : Nat) (rels : List (List Nat))
    (x : Nat) : Bool :=
  andB (allR 0 (Nat.add m m) fun c => Nat.blt (step A (Nat.add m m) x c) N)
  (andB (allR 0 m fun g =>
    andB (Nat.beq (step A (Nat.add m m) (step A (Nat.add m m) x (Nat.add g g))
      (Nat.succ (Nat.add g g))) x)
    (Nat.beq (step A (Nat.add m m) (step A (Nat.add m m) x (Nat.succ (Nat.add g g)))
      (Nat.add g g)) x))
  (relsAt A (Nat.add m m) rels x))

@[expose] noncomputable def coverPointOK (A B : Nat → Nat) (m N : Nat) (R W : List (List Nat))
    (x : Nat) : Bool :=
  andB (allR 0 (Nat.add m m) fun c => Nat.blt (step A (Nat.add m m) x c) N)
  (andB (allR 0 m fun g =>
    andB (Nat.beq (step A (Nat.add m m) (step A (Nat.add m m) x (Nat.add g g))
      (Nat.succ (Nat.add g g))) x)
    (Nat.beq (step A (Nat.add m m) (step A (Nat.add m m) x (Nat.succ (Nat.add g g)))
      (Nat.add g g)) x))
  (andB (List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
      (fun r _ ih k => andB
        (Nat.beq (walk A (Nat.add m m) r x) (B (Nat.add (Nat.mul k N) x)))
        (andB (allR 0 m fun g => Nat.beq
          (B (Nat.add (Nat.mul k N) (step A (Nat.add m m) x (Nat.add g g))))
          (step A (Nat.add m m) (B (Nat.add (Nat.mul k N) x)) (Nat.add g g)))
        (ih (Nat.succ k)))) R 0)
  (relsAt A (Nat.add m m) W x)))

@[expose] noncomputable def cycleFrom (A : Nat → Nat) (L : Nat) (u : List Nat) :
    Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => false)
    (fun k ih y => Bool.rec (motive := fun _ => Bool)
      (andB (notB (Nat.beq (walk A L u y) 0)) (ih (walk A L u y)))
      (Nat.beq (walk A L u y) 0) (Nat.beq k 0))

@[expose] noncomputable def cycleOK (A : Nat → Nat) (L : Nat) (u : List Nat) (ℓ : Nat) : Bool :=
  cycleFrom A L u ℓ 0

@[expose] noncomputable def fixOK (A : Nat → Nat) (L : Nat) (u : List Nat) : Bool :=
  Nat.beq (walk A L u 0) 0

@[expose] noncomputable def movesOK (A : Nat → Nat) (L : Nat) (us : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun u _ ih => andB (notB (fixOK A L u)) ih) us

@[expose] noncomputable def keyOf (A : Nat → Nat) (L N : Nat) (w : List Nat) (base : List Nat) :
    Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun b _ ih acc => ih (Nat.add (Nat.mul acc N) (walk A L w b))) base 0

@[expose] noncomputable def nthW (ws : List (List Nat)) : Nat → List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun w _ ih i => Nat.rec (motive := fun _ => List Nat) w (fun j _ => ih j) i) ws

@[expose] noncomputable def lenL {α : Type} (l : List α) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => Nat.succ ih) l

@[expose] noncomputable def keysInc (A : Nat → Nat) (L N : Nat) (ws : List (List Nat))
    (base : List Nat) (ord : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun i _ ih p => andB (Nat.blt i (lenL ws))
      (andB (Nat.blt p (Nat.succ (keyOf A L N (nthW ws i) base)))
        (ih (Nat.succ (keyOf A L N (nthW ws i) base))))) ord

@[expose] noncomputable def distinctOK (A : Nat → Nat) (L N : Nat) (ws : List (List Nat))
    (base ord : List Nat) : Bool :=
  andB (List.rec (motive := fun _ => Bool) true (fun b _ ih => andB (Nat.blt b N) ih) base)
  (andB (Nat.beq (lenL ord) (lenL ws)) (keysInc A L N ws base ord 0))

end CFSG.KC.MiscCoset.Act

end
