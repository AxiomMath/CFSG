module

public import CFSG.Certificates.Kernel.Orders.Mat3
public import CFSG.Mathlib.Decide.Nodup

public section

namespace CFSG.KD.Asc82Syl

open CFSG.KC.Ord CFSG.KC.Loop

@[expose] noncomputable def LO : Nat := Nat.sub (Nat.shiftLeft 1 36) 1

@[expose] noncomputable def RM : Nat := Nat.sub (Nat.shiftLeft 1 6) 1

@[expose] noncomputable def CI : Nat := rep1 6 6

@[expose] noncomputable def ONE : Nat := rep1 7 6

@[expose] noncomputable def UP : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => Nat.lor acc (Nat.shiftLeft (Nat.sub (Nat.shiftLeft 1 (Nat.sub (Nat.sub 6 i) 1)) 1)
      (Nat.succ (Nat.mul (Nat.succ 6) i)))) 6

@[expose] noncomputable def constsK : Bool := consts3OK 6 4 36 LO RM CI ONE UP

@[expose] noncomputable def MUL (a b : Nat) : Nat := mul3s 6 36 LO CI RM a b

@[expose] noncomputable def negK (X : Nat) : Nat :=
  Nat.lor (Nat.shiftRight X 36) (Nat.shiftLeft (Nat.land X LO) 36)

@[expose] noncomputable def canonK (X : Nat) : Nat := nIf(Nat.blt (negK X) X, negK X, X)

@[expose] noncomputable def eqC (X Y : Nat) : Bool := Nat.beq (canonK X) (canonK Y)

@[expose] noncomputable def wAt (WP e : Nat) : Nat :=
  Nat.land (Nat.shiftRight WP (Nat.mul 72 e)) (Nat.sub (Nat.shiftLeft 1 72) 1)

@[expose] noncomputable def pw (j : Nat) : Nat := Nat.shiftLeft 1 j

@[expose] noncomputable def transK (A T : Nat) : Bool :=
  allBelow 36 1 fun t =>
    (fun s => bAnd(Nat.beq (fld(T, t, 1)) (fld(A, s, 1)),
      Nat.beq (fld(T, Nat.add 36 t, 1)) (fld(A, Nat.add 36 s, 1))))
    (Nat.add (Nat.mul 6 (Nat.mod t 6)) (Nat.div t 6))

@[expose] noncomputable def genK (G : List (Nat × Nat)) (D : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun g _ ih => bAnd(valid3 36 LO g.1, bAnd(valid3 36 LO g.2, bAnd(transK g.1 g.2,
      bAnd((fun s => bIf(Nat.beq s D, true, Nat.beq s (negK D))) (MUL (MUL g.2 D) g.1), ih))))) G

@[expose] noncomputable def enumL (WP : Nat) (G : List (Nat × Nat)) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun g _ ih j => bAnd(allBelow (pw j) 16 fun e =>
      Nat.beq (wAt WP (Nat.add e (pw j))) (MUL (wAt WP e) g.1), ih (Nat.succ j))) G

@[expose] noncomputable def enumK (WP : Nat) (G : List (Nat × Nat)) : Bool :=
  bAnd(Nat.beq (wAt WP 0) ONE, enumL WP G 0)

@[expose] noncomputable def keysL (WP p : Nat) : Nat → List Nat :=
  Nat.rec (motive := fun _ => List Nat) [] (fun e acc => Nat.mod (canonK (wAt WP e)) p :: acc)

@[expose] noncomputable def keyK (WP p n : Nat) : Bool := CFSG.Decide.bitsetNodup (keysL WP p n)

@[expose] noncomputable def conjL (WP k j : Nat) : List Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun c _ ih i => bAnd(Nat.blt c (pw j),
      bAnd(bIf(Nat.blt j k, Nat.beq c (pw i), true),
      bAnd(bIf(Nat.blt i k, Nat.blt c (pw k), true),
      bAnd(eqC (MUL (wAt WP (pw i)) (wAt WP (pw j))) (MUL (wAt WP (pw j)) (wAt WP c)),
        ih (Nat.succ i))))))

@[expose] noncomputable def relL (WP k : Nat) : List (Nat × List Nat) → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun r _ ih j => bAnd(Nat.blt r.1 (pw j),
      bAnd(eqC (MUL (wAt WP (pw j)) (wAt WP (pw j))) (wAt WP r.1),
      bAnd(Nat.beq r.2.length j, bAnd(conjL WP k j r.2 0, ih (Nat.succ j))))))

@[expose] noncomputable def relK (WP k m : Nat) (R : List (Nat × List Nat)) : Bool :=
  bAnd(Nat.beq R.length m, relL WP k R 0)

@[expose] noncomputable def qtK (WP QM QF k q : Nat) : Bool :=
  allBelow (Nat.mul q q) 4 fun t =>
    (fun u v w f => bAnd(Nat.blt f (pw k),
      eqC (MUL (wAt WP (Nat.shiftLeft u k)) (wAt WP (Nat.shiftLeft v k)))
        (wAt WP (Nat.add f (Nat.shiftLeft w k)))))
    (Nat.div t q) (Nat.mod t q) (fld(QM, Nat.mul 4 t, 15)) (fld(QF, Nat.mul 8 t, 255))

@[expose] noncomputable def ctK (WP CT k q : Nat) : Bool :=
  allBelow (Nat.mul q 64) 16 fun t =>
    (fun u f => bIf(Nat.blt f (pw k),
      (fun x y => Nat.beq (fld(CT, t, 1))
        (Bool.rec (motive := fun _ => Nat) 0 1 (eqC (MUL x y) (MUL y x))))
        (wAt WP f) (wAt WP (Nat.shiftLeft u k)), true))
    (Nat.div t 64) (Nat.mod t 64)

@[expose] noncomputable def omK (WP OM k : Nat) : Bool :=
  allBelow (pw k) 1 fun f =>
    Nat.beq (fld(OM, f, 1)) (Bool.rec (motive := fun _ => Nat) 0 1
      (Nat.beq (canonK (MUL (wAt WP f) (wAt WP f))) ONE))

@[expose] noncomputable def qm (QM u v : Nat) : Nat := fld(QM, Nat.mul 4 (Nat.add (Nat.mul 16 u) v), 15)

@[expose] noncomputable def popK (X n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun i acc => Nat.add acc (fld(X, i, 1))) n

@[expose] noncomputable def extK (QM q X x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) X
    (fun h acc => nIf(Nat.beq (fld(X, h, 1)) 1, Nat.lor acc (Nat.shiftLeft 1 (qm QM x h)), acc)) q

@[expose] noncomputable def commX (QM q X x : Nat) : Bool :=
  allBelow q 1 fun h => bIf(Nat.beq (fld(X, h, 1)) 1, Nat.beq (qm QM x h) (qm QM h x), true)

@[expose] noncomputable def memF (F : List (Nat × List Nat)) (X : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun r _ ih => bIf(Nat.beq r.1 X, true, ih)) F

@[expose] noncomputable def closX (F : List (Nat × List Nat)) (QM q X : Nat) : Bool :=
  allBelow q 1 fun x =>
    bIf(bAnd(Nat.beq (fld(X, x, 1)) 0, bAnd(Nat.beq (fld(X, qm QM x x, 1)) 1, commX QM q X x)),
      memF F (extK QM q X x), true)

@[expose] noncomputable def cents (CT k : Nat) (gens : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (Nat.sub (pw (pw k)) 1)
    (fun g _ ih => Nat.land ih (fld(CT, Nat.mul 64 g, Nat.sub (Nat.shiftLeft 1 64) 1))) gens

@[expose] noncomputable def subX (q X : Nat) (gens : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun g _ ih => bAnd(Nat.blt g q, bAnd(Nat.beq (fld(X, g, 1)) 1, ih))) gens

@[expose] noncomputable def recK (F : List (Nat × List Nat)) (QM CT OM k q bound : Nat)
    (flag : Bool) (X : Nat) (gens : List Nat) : Bool :=
  bAnd(Nat.blt X (pw q), bAnd(subX q X gens,
    bAnd(Nat.ble (Nat.mul (popK (Bool.rec (motive := fun _ => Nat) (cents CT k gens)
        (Nat.land (cents CT k gens) OM) flag) (pw k)) (popK X q)) bound,
      closX F QM q X)))

@[expose] noncomputable def famK (F : List (Nat × List Nat)) (QM CT OM k q bound : Nat)
    (flag : Bool) : Bool :=
  bAnd(memF F 1, List.rec (motive := fun _ => Bool) true
    (fun r _ ih => bAnd(recK F QM CT OM k q bound flag r.1 r.2, ih)) F)

end CFSG.KD.Asc82Syl

end
