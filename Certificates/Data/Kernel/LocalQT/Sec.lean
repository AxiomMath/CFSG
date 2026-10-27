module

public import CFSG.Certificates.Kernel.Orders.Mat

public section

namespace CFSG.KC.LQT

open CFSG.KC.Ord

structure Lay where
  p : Nat
  w : Nat
  S : Nat
  d : Nat
  T : Nat
  L : Nat
  H : Nat
  CM : Nat
  RM : Nat
  ONE : Nat
  LV : Nat
  HV : Nat

@[expose] noncomputable def Lay.ok (c : Lay) : Bool :=
  constsOK c.p c.w c.S c.d c.T c.L c.H c.CM c.RM c.ONE c.LV c.HV

@[expose] noncomputable def Lay.mul (c : Lay) (A B : Nat) : Nat :=
  mulR c.p c.w c.S c.d c.T c.L c.H c.CM c.RM A B

@[expose] noncomputable def Lay.vec (c : Lay) (v M : Nat) : Nat :=
  vecR c.p c.w c.S c.d c.T c.LV c.HV c.RM v M

@[expose] noncomputable def Lay.unit (c : Lay) (t : Nat) : Nat :=
  Nat.shiftLeft (nat_lit 1) (Nat.mul c.w t)

@[expose] noncomputable def Lay.pow (c : Lay) (X e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) c.ONE (fun _ acc => c.mul acc X) e

@[expose] noncomputable def Lay.vpow (c : Lay) (X v e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) v (fun _ acc => c.vec acc X) e

@[expose] noncomputable def strictB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def isWs (n : Nat) : Bool :=
  orB (Nat.beq n (nat_lit 32)) (andB (Nat.ble (nat_lit 9) n) (Nat.ble n (nat_lit 13)))

@[expose] noncomputable def digitV (n : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.sub n (nat_lit 48))
    (andB (Nat.ble (nat_lit 48) n) (Nat.ble n (nat_lit 57)))

@[expose] noncomputable def decRun (c : Lay) (M : Nat) (l : List Char) :
    Nat → Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat → Bool)
    (fun _ i _ acc => Nat.beq (Nat.shiftRight M (Nat.mul c.S i)) acc)
    (fun ch _ ih ph i j acc => strictB (Char.toNat ch) fun n =>
      Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) (ih (nat_lit 0) i j acc) (ih (nat_lit 1) i j acc)
          (Nat.beq n (nat_lit 10)))
        (Bool.rec (motive := fun _ => Bool)
          (Bool.rec (motive := fun _ => Bool)
            (strictB (Nat.add acc (Nat.shiftLeft (Nat.mod (digitV n) c.p) (Nat.mul c.w j)))
              fun a => strictB (Nat.succ j) fun j1 =>
                Bool.rec (motive := fun _ => Bool) (ih (nat_lit 1) i j1 a)
                  (andB (Nat.beq (rowsOf c.S i (nat_lit 1) M) a)
                    (strictB (Nat.succ i) fun i1 => ih (nat_lit 1) i1 (nat_lit 0) (nat_lit 0)))
                  (Nat.beq j1 c.d))
            (ih (nat_lit 1) i j acc) (Nat.ble c.d i))
          (ih (nat_lit 1) i j acc) (isWs n))
        (Nat.beq ph (nat_lit 1)))
    l

@[expose] noncomputable def decOK (c : Lay) (M : Nat) (l : List Char) : Bool :=
  decRun c M l (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def stepOK (c : Lay) (V P : Nat → Nat) (n : Nat) : Bool :=
  strictB (P n) fun q => strictB (Nat.land q (nat_lit 1048575)) fun a =>
    strictB (Nat.shiftRight q (nat_lit 20)) fun b =>
      andB (Nat.blt a n) (andB (Nat.blt b n) (Nat.beq (V n) (c.mul (V a) (V b))))

@[expose] noncomputable def allLt (m : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i ih => andB (f i) ih) m

@[expose] noncomputable def digApp (c : Lay) (b : Nat) (X : Nat → Nat) (m : Nat) :
    Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun _ _ v => v)
    (fun _ ih i n v => ih (Nat.succ i) (Nat.div n b) (c.vpow (X i) v (Nat.mod n b))) m

@[expose] noncomputable def elemOK (c : Lay) (V : Nat → Nat) (N : Nat) (O W : Nat → Nat)
    (r : Nat) : Bool :=
  andB (allLt r fun i => Nat.blt (O i) N)
  (andB (allLt r fun i => Nat.beq (c.mul (c.mul (V (O i)) (V (O i))) (V (O i))) c.ONE)
  (andB (allLt r fun i => allLt i fun j =>
      Nat.beq (c.mul (V (O i)) (V (O j))) (c.mul (V (O j)) (V (O i))))
    (allLt (Nat.sub (Nat.pow (nat_lit 3) r) (nat_lit 1)) fun n => strictB (W (Nat.succ n)) fun t =>
      andB (Nat.blt t c.d) (notB (Nat.beq
        (digApp c (nat_lit 3) (fun i => V (O i)) r (nat_lit 0) (Nat.succ n) (c.unit t))
        (c.unit t))))))

@[expose] noncomputable def sortRun (N : Nat) (f : Nat → Nat) (σ : List Nat) : Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Bool)
    (fun _ mask => Nat.beq mask (Nat.sub (Nat.shiftLeft (nat_lit 1) N) (nat_lit 1)))
    (fun k _ ih lo mask => strictB (f k) fun v =>
      andB (Nat.blt k N) (andB (Nat.beq (Nat.land mask (Nat.shiftLeft (nat_lit 1) k)) (nat_lit 0))
        (andB (Nat.ble lo v) (strictB (Nat.lor mask (Nat.shiftLeft (nat_lit 1) k)) fun m1 =>
          ih (Nat.succ v) m1))))
    σ

@[expose] noncomputable def normalOK (c : Lay) (b : Nat) (X : Nat → Nat) (m t : Nat)
    (σ : List Nat) : Bool :=
  andB (Nat.blt t c.d)
    (sortRun (Nat.pow b m) (fun n => digApp c b X m (nat_lit 0) n (c.unit t)) σ (nat_lit 0) (nat_lit 0))

@[expose] noncomputable def sel3 (X Y Z i : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) Z Y (Nat.beq i (nat_lit 1))) X
    (Nat.beq i (nat_lit 0))

@[expose] noncomputable def conjOK (c : Lay) (H X W : Nat) : Bool :=
  Nat.beq (c.mul H X) (c.mul W H)

@[expose] noncomputable def sqOK (c : Lay) (V : Nat → Nat) (N ix iy ih r oh a b cc dd t : Nat)
    (σ : List Nat) : Bool :=
  andB (Nat.blt ix N) (andB (Nat.blt iy N) (andB (Nat.blt ih N)
  (andB (Nat.blt (nat_lit 0) r) (andB (Nat.blt (nat_lit 0) oh)
  (andB (Nat.beq (c.pow (V ix) r) c.ONE) (andB (Nat.beq (c.pow (V iy) r) c.ONE)
  (andB (Nat.beq (c.pow (V ih) oh) c.ONE)
  (andB (Nat.beq (c.mul (V ix) (V iy)) (c.mul (V iy) (V ix)))
  (andB (conjOK c (V ih) (V ix) (c.mul (c.pow (V ix) a) (c.pow (V iy) cc)))
  (andB (conjOK c (V ih) (V iy) (c.mul (c.pow (V ix) b) (c.pow (V iy) dd)))
    (normalOK c r (sel3 (V ix) (V iy) (V iy)) (nat_lit 2) t σ)))))))))))

@[expose] noncomputable def commM (c : Lay) (r X Y : Nat) : Nat :=
  c.mul (c.mul (c.mul X Y) (c.pow X (Nat.sub r (nat_lit 1)))) (c.pow Y (Nat.sub r (nat_lit 1)))

@[expose] noncomputable def cubOK (c : Lay) (V : Nat → Nat) (N ix iy ih r oh a b cc dd k l μ t : Nat)
    (σ : List Nat) : Bool :=
  andB (Nat.blt ix N) (andB (Nat.blt iy N) (andB (Nat.blt ih N)
  (andB (Nat.blt (nat_lit 0) r) (andB (Nat.blt (nat_lit 0) oh)
  (andB (Nat.beq (c.pow (V ix) r) c.ONE) (andB (Nat.beq (c.pow (V iy) r) c.ONE)
  (andB (Nat.beq (c.pow (V ih) oh) c.ONE)
  (strictB (commM c r (V ix) (V iy)) fun Z =>
  (andB (notB (Nat.beq (c.vec (c.unit t) Z) (c.unit t)))
  (andB (Nat.beq (c.mul Z (V ix)) (c.mul (V ix) Z))
  (andB (Nat.beq (c.mul Z (V iy)) (c.mul (V iy) Z))
  (andB (conjOK c (V ih) (V ix) (c.mul (c.mul (c.pow (V ix) a) (c.pow (V iy) b)) (c.pow Z k)))
  (andB (conjOK c (V ih) (V iy) (c.mul (c.mul (c.pow (V ix) cc) (c.pow (V iy) dd)) (c.pow Z l)))
  (andB (conjOK c (V ih) Z (c.pow Z μ))
    (normalOK c r (sel3 (V ix) (V iy) Z) (nat_lit 3) t σ)))))))))))))))

@[expose] noncomputable def enumOK (c : Lay) (V E PL CL : Nat → Nat) (n k1 k2 : Nat) : Bool :=
  andB (Nat.blt 0 n) (andB (Nat.beq (V (E 0)) c.ONE)
  (andB (allLt (Nat.sub n 1) fun i0 => strictB (Nat.succ i0) fun i => strictB (PL i) fun q =>
      strictB (Nat.land q 1048575) fun p => strictB (Nat.shiftRight q 20) fun l =>
        andB (Nat.blt p i) (andB (Nat.blt l 2) (Nat.beq (V (E i))
          (c.mul (V (E p)) (Bool.rec (motive := fun _ => Nat) (V k2) (V k1) (Nat.beq l 0))))))
    (allLt n fun i => andB
      (strictB (CL (Nat.mul 2 i)) fun j => andB (Nat.blt j n) (Nat.beq (c.mul (V (E i)) (V k1)) (V (E j))))
      (strictB (CL (Nat.succ (Nat.mul 2 i))) fun j =>
        andB (Nat.blt j n) (Nat.beq (c.mul (V (E i)) (V k2)) (V (E j)))))))

@[expose] noncomputable def notMemOK (c : Lay) (V E : Nat → Nat) (n t X : Nat) : Bool :=
  strictB (c.vec (c.unit t) X) fun v => allLt n fun i => notB (Nat.beq v (c.vec (c.unit t) (V (E i))))

@[expose] noncomputable def locOK (c : Lay) (V I E PL CL : Nat → Nat) (N n t ok1 ok2 oh a b cc dd : Nat)
    (σq σe : List Nat) : Bool :=
  andB (allLt 10 fun k => Nat.blt (I k) N)
  (andB (enumOK c V E PL CL n (I 0) (I 1))
  (andB (sortRun n (fun i => c.vec (c.unit t) (V (E i))) σe 0 0)
  (andB (allLt 8 fun k => Nat.blt (I (Nat.add k 10)) n)
  (andB (Nat.beq (V (I 2)) (V (E (I 10)))) (andB (Nat.beq (V (I 3)) (V (E (I 11))))
  (andB (Nat.beq (V (I 6)) (V (E (I 12)))) (andB (Nat.beq (V (I 7)) (V (E (I 13))))
  (andB (Nat.beq (V (I 8)) (V (E (I 14)))) (andB (Nat.beq (V (I 9)) (V (E (I 15))))
  (andB (Nat.blt 0 ok1) (andB (Nat.blt 0 ok2) (andB (Nat.beq (c.pow (V (I 0)) ok1) c.ONE)
  (andB (Nat.beq (c.pow (V (I 1)) ok2) c.ONE)
  (andB (Nat.beq (c.pow (V (I 2)) 3) c.ONE) (andB (Nat.beq (c.pow (V (I 3)) 3) c.ONE)
  (andB (Nat.beq (c.mul (V (I 2)) (V (I 3))) (c.mul (V (I 3)) (V (I 2))))
  (andB (normalOK c 3 (sel3 (V (I 2)) (V (I 3)) (V (I 3))) 2 t σq)
  (andB (Nat.blt 0 oh) (andB (Nat.beq (c.pow (V (I 4)) oh) c.ONE)
  (andB (conjOK c (V (I 4)) (V (I 0)) (V (E (I 16))))
  (andB (conjOK c (V (I 4)) (V (I 1)) (V (E (I 17))))
  (andB (conjOK c (V (I 4)) (V (I 2)) (c.mul (c.pow (V (I 2)) a) (c.pow (V (I 3)) cc)))
  (andB (conjOK c (V (I 4)) (V (I 3)) (c.mul (c.pow (V (I 2)) b) (c.pow (V (I 3)) dd)))
  (andB (Nat.beq (c.pow (V (I 5)) 3) c.ONE)
  (andB (notB (Nat.beq (c.vec (c.unit t) (V (I 5))) (c.unit t)))
  (andB (Nat.beq (c.mul (V (I 5)) (V (I 0))) (c.mul (V (I 0)) (V (I 5))))
  (andB (Nat.beq (c.mul (V (I 5)) (V (I 1))) (c.mul (V (I 1)) (V (I 5))))
  (andB (notMemOK c V E n t (V (I 5)))
  (andB (notMemOK c V E n t (c.mul (V (I 5)) (V (I 5))))
  (andB (Nat.beq (c.mul (V (I 6)) (V (I 7))) (c.mul (c.mul (V (I 0)) (V (I 7))) (V (I 6))))
    (Nat.beq (c.mul (V (I 8)) (V (I 9))) (c.mul (c.mul (V (I 1)) (V (I 9))) (V (I 8))))))))))))))))))))))))))))))))))

end CFSG.KC.LQT

end
