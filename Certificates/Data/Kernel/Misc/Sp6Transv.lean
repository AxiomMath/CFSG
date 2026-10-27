module

public import Certificates.Data.Kernel.Sp62Twin
public import Certificates.Data.Kernel.Misc.PermClos

public section

namespace CFSG.KC.Misc.Sp6Transv

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KD.Sp62 CFSG.KC.Misc.Clos

@[expose] noncomputable def letN (y : Nat) (k : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def commF (x y : Nat) : Bool := Nat.beq (MULF x y) (MULF y x)

@[expose] noncomputable def conjF (g gi x : Nat) : Nat := MULF (MULF g x) gi

@[expose] noncomputable def interAt (E S EQ NB : Nat → Nat) (c ci k : Nat) : Bool :=
  letB (E k) fun x => letB (NB k) fun r =>
    Bool.rec (motive := fun _ => Bool)
      (letB (MULF (MULF ci x) c) fun y =>
        andB (Nat.ble r 512)
          (andB (impB (Nat.blt 0 r) (Nat.blt (E (S (Nat.pred r))) y))
            (impB (Nat.blt r 512) (Nat.blt y (E (S r))))))
      (letB (Nat.sub r 1048576) fun j => andB (Nat.blt j 32) (Nat.beq (EQ j) x))
      (Nat.ble 1048576 r)

@[expose] noncomputable def cntR (n : Nat) (f : Nat → Bool) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => Bool.rec (motive := fun _ => Nat) acc (Nat.succ acc) (f i)) n

@[expose] noncomputable def spanG (EQ SQ SK K KI : Nat → Nat) (m l : Nat) : Nat :=
  letN (SK (Nat.add (Nat.mul 5 m) l)) fun k => conjF (K k) (KI k) (EQ (SQ m))

@[expose] noncomputable def spanAt (EQ SQ SK K KI SE SP SS : Nat → Nat) (m : Nat) : Bool :=
  andB (Nat.blt (SQ m) 32)
    (andB (allN 5 fun l => Nat.blt (SK (Nat.add (Nat.mul 5 m) l)) 12)
      (andB (allR 0 32 (treeAt MULF ONE (spanG EQ SQ SK K KI m) 5
          (fun k => SE (Nat.add (Nat.mul 32 m) k)) (fun k => SP (Nat.add (Nat.mul 32 m) k))))
        (allR 0 32 (sortAt 32 (fun k => SE (Nat.add (Nat.mul 32 m) k))
          (fun k => SS (Nat.add (Nat.mul 32 m) k))))))

@[expose] noncomputable def coverQ (EQ SQ : Nat → Nat) (s : Nat) : Bool :=
  allN 32 fun i => orB (Nat.beq (EQ i) ONE) (orB (Nat.beq (EQ i) s)
    (anyN 30 fun m => Nat.beq (SQ m) i))

@[expose] noncomputable def abelQ (EQ : Nat → Nat) : Bool :=
  allN 32 fun i => andB (Nat.beq (MULF (EQ i) (EQ i)) ONE) (allN 32 fun j => commF (EQ i) (EQ j))

@[expose] noncomputable def countQ (EQ : Nat → Nat) (z0 z2 : Nat) : Bool :=
  andB (Nat.beq (cntR 32 fun i => commF (EQ i) z0) 8)
    (andB (Nat.beq (cntR 32 fun i => commF (EQ i) z2) 8)
      (andB (Nat.beq (cntR 32 fun i => andB (commF (EQ i) z0) (commF (EQ i) z2)) 2)
        (andB (Nat.beq (cntR 32 fun i => commF (EQ i) (MULF z0 z2)) 2)
          (Nat.beq (cntR 32 fun i => commF (EQ i) (MULF z0 (MULF z2 z2))) 2))))

@[expose] noncomputable def invAt (K KI : Nat → Nat) (k : Nat) : Bool :=
  andB (Nat.blt (KI k) 68719476736) (Nat.beq (MULF (K k) (KI k)) ONE)

@[expose] noncomputable def wordF (L : Nat → Nat) (n v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => ONE)
    (fun _ ih v => MULF (L (Nat.mod v 8)) (ih (Nat.div v 8))) n v

@[expose] noncomputable def wordI (LI : Nat → Nat) (n v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => ONE)
    (fun _ ih v => MULF (ih (Nat.div v 8)) (LI (Nat.mod v 8))) n v

@[expose] noncomputable def wElt (Z0 Z1 Z2 T w : Nat) : Nat :=
  MULF (VC Z0 Z1 Z2 (Nat.div w 27) (Nat.mod (Nat.div w 9) 3) (Nat.mod (Nat.div w 3) 3))
    (PW T (Nat.mod w 3))

@[expose] noncomputable def wordAt (Z0 Z1 Z2 T : Nat) (L LI REP WR : Nat → Nat) (w : Nat) : Bool :=
  letB (wElt Z0 Z1 Z2 T w) fun x => letB (WR w) fun r =>
    Nat.rec (motive := fun _ => Bool)
      (orB (Bool.not (Nat.beq (MULF (MULF x x) x) ONE)) (Nat.beq x ONE))
      (fun r' _ => letB (Nat.mod r' 4) fun ri => letB (Nat.div r' 4) fun nv =>
        letB (Nat.mod nv 16) fun n => letB (Nat.div nv 16) fun v =>
          andB (Nat.blt ri 3)
            (Nat.beq (MULF (MULF (wordI LI n v) x) (wordF L n v)) (REP ri))) r

@[expose] noncomputable def filtAt (R : Nat → Nat) (s z1 z1s z2 a1 a2 t : Nat) : Bool :=
  letB (recX R 38 t) fun x =>
    orB (Bool.not (andB (commF x z2) (andB (Nat.beq (MULF x x) ONE)
      (andB (Bool.not (Nat.beq x ONE)) (Nat.beq (MULF (MULF x z1) x) z1s)))))
      (orB (Nat.beq x s) (orB (Nat.beq x a1) (Nat.beq x a2)))

end CFSG.KC.Misc.Sp6Transv

end
