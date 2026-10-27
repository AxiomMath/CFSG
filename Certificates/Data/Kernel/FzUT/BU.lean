module

public import Certificates.Data.Kernel.FzUT.Codes

public section

namespace CFSG.KC.FzUT

@[expose] noncomputable def allB (n : Nat) (p : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun i acc => Bool.rec (motive := fun _ => Bool) false acc (p i)) n

@[expose] noncomputable def cntB (n : Nat) (p : Nat → Bool) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => Bool.rec (motive := fun _ => Nat) acc (Nat.succ acc) (p i)) n

@[expose] noncomputable def andB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) false b a

@[expose] noncomputable def orB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) b true a

@[expose] noncomputable def impB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) true b a

@[expose] noncomputable def allL (l : List Nat) (p : Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ acc => andB (p x) acc) l

@[expose] noncomputable def anyL (l : List Nat) (p : Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun x _ acc => orB (p x) acc) l

@[expose] noncomputable def fld (e i : Nat) : Nat := Nat.land (Nat.shiftRight e (Nat.mul 6 i)) 63

@[expose] noncomputable def rhoBP (x : Nat) : Nat :=
  Nat.add (Nat.add (f4mulP 2 (Nat.land x 3))
      (Nat.mul 4 (f4mulP 2 (Nat.land (Nat.shiftRight x 2) 3))))
    (Nat.mul 16 (f4mulP 3 (Nat.shiftRight x 4)))

@[expose] noncomputable def cfP (u v x : Nat) : Nat := evN u (rhoBP u) v (rhoBP v) x

@[expose] noncomputable def yfP (u v x : Nat) : Nat := evN u (rhoBP (rhoBP u)) v (rhoBP (rhoBP v)) x

@[expose] noncomputable def isInvP (x : Nat) : Bool := andB (Nat.blt 0 x) (Nat.beq (pmulP x x) 0)

@[expose] noncomputable def qOK (u v : Nat) : Bool :=
  andB (Nat.beq (cfP (cfP u v u) (cfP u v v) (cfP u v u)) 1)
    (andB (Nat.beq (cfP (cfP u v u) (cfP u v v) (cfP u v v)) 4)
      (Nat.beq (cntB 64 (fun x => Nat.beq (cfP u v (cfP u v x)) x)) 16))

@[expose] noncomputable def it3 (f : Nat → Nat) (x : Nat) : Nat := f (f (f x))

@[expose] noncomputable def sOK (u v b1 b3 : Nat) : Bool :=
  let q := cfP u v
  let s := cfP b1 b3
  andB (orB (andB (Nat.beq (s b1) 1) (Nat.beq (s b3) 4))
    (orB (andB (Nat.beq (s b1) (q 1)) (Nat.beq (s b3) (q 4)))
    (orB (andB (Nat.beq (s b1) (q (q 1))) (Nat.beq (s b3) (q (q 4))))
      (andB (Nat.beq (s b1) (it3 q 1)) (Nat.beq (s b3) (it3 q 4))))))
  (andB (orB (andB (Nat.beq (s (q 1)) (q b1)) (Nat.beq (s (q 4)) (q b3)))
      (andB (Nat.beq (s (q 1)) (it3 q b1)) (Nat.beq (s (q 4)) (it3 q b3))))
    (allB 64 (fun x => impB (Nat.beq (q (q x)) x) (Nat.beq (pmulP (s x) x) 0))))

@[expose] noncomputable def noS (u v : Nat) : Bool :=
  allB 4 (fun z1 => allB 4 (fun z3 =>
    Bool.rec (motive := fun _ => Bool) true false
      (sOK u v (Nat.add 1 (Nat.mul 16 z1)) (Nat.add 4 (Nat.mul 16 z3)))))

@[expose] noncomputable def yOK (b1 b3 c1 c3 : Nat) : Bool :=
  let q := cfP 4 17
  let s := cfP b1 b3
  let y := yfP c1 c3
  andB (Nat.beq (y c1) 1) (andB (Nat.beq (y c3) 4) (andB (Nat.beq (y 17) (q c3))
    (andB (Nat.beq (y b1) (s c1)) (Nat.beq (y b3) (s c3)))))

@[expose] noncomputable def tabP (f : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => Nat.lor acc (Nat.shiftLeft (f i) (Nat.mul 6 i))) 64

@[expose] noncomputable def atP (T x : Nat) : Nat := fld T x

@[expose] noncomputable def hAutT (T : Nat) : Bool :=
  andB (Nat.beq (atP T 0) 0)
  (andB (allB 64 (fun x => impB (Nat.beq (atP T x) 0) (Nat.beq x 0)))
  (andB (allB 64 (fun x =>
      andB (Nat.beq (atP T (pmulP 1 x)) (pmulP (atP T 1) (atP T x)))
      (andB (Nat.beq (atP T (pmulP 2 x)) (pmulP (atP T 2) (atP T x)))
      (andB (Nat.beq (atP T (pmulP 4 x)) (pmulP (atP T 4) (atP T x)))
        (Nat.beq (atP T (pmulP 8 x)) (pmulP (atP T 8) (atP T x)))))))
    (andB (Nat.beq (atP T 2) (rhoBP (atP T 1))) (andB (Nat.beq (atP T 3) (rhoBP (atP T 2)))
      (andB (Nat.beq (atP T 8) (rhoBP (atP T 4))) (Nat.beq (atP T 12) (rhoBP (atP T 8))))))))

@[expose] noncomputable def buConjOK (h1 h3 k1 k3 : Nat) (f : Nat → Nat) (r1 r3 : Nat) : Bool :=
  andB (Nat.beq (cfP h1 h3 (f k1)) r1) (Nat.beq (cfP h1 h3 (f k3)) r3)

@[expose] noncomputable def buRecOK (h1 h3 k1 k3 : Nat) : Bool :=
  andB (hAutT (tabP (cfP h1 h3))) (andB (Nat.beq (cfP h1 h3 k1) 1) (Nat.beq (cfP h1 h3 k3) 4))

@[expose] noncomputable def l1OK (e : Nat) : Bool :=
  andB (buRecOK (fld e 2) (fld e 3) (fld e 4) (fld e 5))
    (buConjOK (fld e 2) (fld e 3) (fld e 4) (fld e 5) (cfP (fld e 0) (fld e 1)) 4 17)

@[expose] noncomputable def repSY (c i : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (fld 12995873 i) (fun _ _ => fld 1053953 i) c

@[expose] noncomputable def l2OK (e : Nat) : Bool :=
  andB (Nat.blt (fld e 4) 2)
  (andB (buRecOK (fld e 5) (fld e 6) (fld e 7) (fld e 8))
  (andB (buConjOK (fld e 5) (fld e 6) (fld e 7) (fld e 8) (cfP 4 17) 4 17)
  (andB (buConjOK (fld e 5) (fld e 6) (fld e 7) (fld e 8) (cfP (fld e 0) (fld e 1))
      (repSY (fld e 4) 0) (repSY (fld e 4) 1))
    (buConjOK (fld e 5) (fld e 6) (fld e 7) (fld e 8) (yfP (fld e 2) (fld e 3))
      (repSY (fld e 4) 2) (repSY (fld e 4) 3)))))

@[expose] noncomputable def stage1 (L1 : List Nat) : Bool :=
  allB 64 (fun u => allB 64 (fun v =>
    impB (andB (isInvP u) (andB (isInvP v) (qOK u v)))
      (orB (anyL L1 (fun e => andB (Nat.beq (fld e 0) u) (Nat.beq (fld e 1) v))) (noS u v))))

@[expose] noncomputable def stage2 (L2 : List Nat) : Bool :=
  allB 4 (fun z1 => allB 4 (fun z3 =>
    impB (sOK 4 17 (Nat.add 1 (Nat.mul 16 z1)) (Nat.add 4 (Nat.mul 16 z3)))
      (allB 64 (fun c1 =>
        impB (yOK (Nat.add 1 (Nat.mul 16 z1)) (Nat.add 4 (Nat.mul 16 z3)) c1 (cfP 4 17 c1))
          (anyL L2 (fun e => andB (Nat.beq (fld e 0) (Nat.add 1 (Nat.mul 16 z1)))
            (andB (Nat.beq (fld e 1) (Nat.add 4 (Nat.mul 16 z3)))
            (andB (Nat.beq (fld e 2) c1) (Nat.beq (fld e 3) (cfP 4 17 c1))))))))))

end CFSG.KC.FzUT
