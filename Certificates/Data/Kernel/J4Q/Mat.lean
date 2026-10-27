module

public import CFSG.Certificates.Kernel.Common.Loop
public import Certificates.Data.CFSGNative.J4.F2

public section

namespace CFSG.KC.J4Q

open CFSG.KC.Loop CFSG.Sporadic.J4.Native

@[expose] noncomputable def andB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) false b a

@[expose] noncomputable def orB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) b true a

@[expose] noncomputable def notB (b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) true false b

@[expose] noncomputable def neN (a b : Nat) : Bool := notB (Nat.beq a b)

@[expose] noncomputable def rep (x s n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft x (Nat.mul s i))) n

@[expose] noncomputable def tmask (k : Nat) : Nat :=
  (fun s => (fun row => Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun r acc => Bool.rec (motive := fun _ => Nat) acc
        (Nat.lor acc (Nat.shiftLeft row (Nat.mul (nat_lit 128) r)))
        (Nat.beq (Nat.land r s) (nat_lit 0))) (nat_lit 128))
    (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun c acc => Bool.rec (motive := fun _ => Nat) (Nat.lor acc (Nat.shiftLeft (nat_lit 1) c)) acc
        (Nat.beq (Nat.land c s) (nat_lit 0))) (nat_lit 128)))
  (Nat.shiftLeft (nat_lit 1) k)

@[expose] noncomputable def padMask : Nat :=
  rep (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 128)) (Nat.shiftLeft (nat_lit 1) (nat_lit 112)))
    (nat_lit 128) (nat_lit 112)

@[expose] noncomputable def canonJ (pad M : Nat) : Bool :=
  andB (Nat.blt M (Nat.shiftLeft (nat_lit 1) (nat_lit 14336))) (Nat.beq (Nat.land M pad) (nat_lit 0))

@[expose] noncomputable def constsOK (c rm one pad t0 t1 t2 t3 t4 t5 t6 : Nat) : Bool :=
  andB (Nat.beq c (rep (nat_lit 1) (nat_lit 128) (nat_lit 112)))
  (andB (Nat.beq pad padMask)
  (andB (Nat.beq rm (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 112)) (nat_lit 1)))
  (andB (Nat.beq one (rep (nat_lit 1) (nat_lit 129) (nat_lit 112)))
  (andB (Nat.beq t0 (tmask (nat_lit 0))) (andB (Nat.beq t1 (tmask (nat_lit 1)))
  (andB (Nat.beq t2 (tmask (nat_lit 2))) (andB (Nat.beq t3 (tmask (nat_lit 3)))
  (andB (Nat.beq t4 (tmask (nat_lit 4))) (andB (Nat.beq t5 (tmask (nat_lit 5)))
    (Nat.beq t6 (tmask (nat_lit 6))))))))))))

@[expose] noncomputable def mstep (c rm A B acc k : Nat) : Nat :=
  Nat.xor acc (Nat.land (Nat.mul (Nat.land (Nat.shiftRight A k) c) rm)
    (Nat.mul (Nat.land (Nat.shiftRight B (Nat.mul k (nat_lit 128))) rm) c))

@[expose] noncomputable def mulJ (c rm A B : Nat) : Nat :=
  strictN A fun a => strictN B fun b =>
    Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun k acc => mstep c rm a b acc k) (nat_lit 112)

@[expose] noncomputable def rowJ (rm M r : Nat) : Nat :=
  Nat.land (Nat.shiftRight M (Nat.mul r (nat_lit 128))) rm

@[expose] noncomputable def vecJ (rm v M : Nat) : Nat :=
  strictN v fun x => strictN M fun m =>
    Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun k acc => Nat.xor acc (Nat.mul (Nat.land (Nat.shiftRight x k) (nat_lit 1)) (rowJ rm m k)))
      (nat_lit 112)

@[expose] noncomputable def powJ (c rm one M e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) one (fun _ acc => strictN acc fun a => mulJ c rm a M) e

@[expose] noncomputable def trLvl (s m x : Nat) : Nat :=
  strictN x fun y => strictN (Nat.land (Nat.xor y (Nat.shiftRight y (Nat.mul (nat_lit 127) s))) m)
    fun t => Nat.xor y (Nat.lor t (Nat.shiftLeft t (Nat.mul (nat_lit 127) s)))

@[expose] noncomputable def trJ (t0 t1 t2 t3 t4 t5 t6 x : Nat) : Nat :=
  trLvl (nat_lit 1) t0 (trLvl (nat_lit 2) t1 (trLvl (nat_lit 4) t2 (trLvl (nat_lit 8) t3
    (trLvl (nat_lit 16) t4 (trLvl (nat_lit 32) t5 (trLvl (nat_lit 64) t6 x))))))

@[expose] noncomputable def getN (d : Nat) (l : List Nat) (i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => d)
    (fun m _ ih i => Nat.rec (motive := fun _ => Nat) m (fun j _ => ih j) i) l i

@[expose] noncomputable def letJ (one : Nat) (mats invs : List Nat) (l : Int) : Nat :=
  Int.rec (motive := fun _ => Nat)
    (fun n => Nat.rec (motive := fun _ => Nat) (getN one invs (nat_lit 0))
      (fun k _ => getN one mats k) n)
    (fun n => getN one invs n)
    l

@[expose] noncomputable def wordFrom (c rm one : Nat) (mats invs : List Nat) (w : List Int) :
    Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun l _ ih acc => strictN (mulJ c rm acc (letJ one mats invs l)) ih) w

@[expose] noncomputable def wordJ (c rm one : Nat) (mats invs : List Nat) (w : List Int) : Nat :=
  wordFrom c rm one mats invs w one

@[expose] noncomputable def strictB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def isWs (n : Nat) : Bool :=
  orB (Nat.beq n (nat_lit 32)) (orB (Nat.beq n (nat_lit 9)) (orB (Nat.beq n (nat_lit 10))
    (orB (Nat.beq n (nat_lit 13)) (orB (Nat.beq n (nat_lit 11)) (Nat.beq n (nat_lit 12))))))

@[expose] noncomputable def ent2 (n : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.land (Nat.sub n (nat_lit 48)) (nat_lit 1))
    (andB (Nat.ble (nat_lit 48) n) (Nat.ble n (nat_lit 57)))

@[expose] noncomputable def row128 (M i : Nat) : Nat :=
  Nat.land (Nat.shiftRight M (Nat.mul (nat_lit 128) i))
    (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 128)) (nat_lit 1))

@[expose] noncomputable def decRun (M : Nat) (l : List Char) : Nat → Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat → Bool)
    (fun _ i _ acc => Nat.beq (Nat.shiftRight M (Nat.mul (nat_lit 128) i)) acc)
    (fun ch _ ih ph i j acc => strictB (Char.toNat ch) fun n =>
      Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) (ih (nat_lit 0) i j acc) (ih (nat_lit 1) i j acc)
          (Nat.beq n (nat_lit 10)))
        (Bool.rec (motive := fun _ => Bool)
          (Bool.rec (motive := fun _ => Bool)
            (strictB (Nat.add acc (Nat.shiftLeft (ent2 n) j)) fun a => strictB (Nat.succ j) fun j1 =>
              Bool.rec (motive := fun _ => Bool) (ih (nat_lit 1) i j1 a)
                (andB (Nat.beq (row128 M i) a)
                  (strictB (Nat.succ i) fun i1 => ih (nat_lit 1) i1 (nat_lit 0) (nat_lit 0)))
                (Nat.beq j1 (nat_lit 112)))
            (ih (nat_lit 1) i j acc) (Nat.ble (nat_lit 112) i))
          (ih (nat_lit 1) i j acc) (isWs n))
        (Nat.beq ph (nat_lit 1)))
    l

@[expose] noncomputable def decOK (M : Nat) (l : List Char) : Bool :=
  decRun M l (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def v2N (v : V2) : Nat :=
  Nat.lor (UInt64.toNat v.lo) (Nat.shiftLeft (UInt64.toNat v.hi) (nat_lit 64))

@[expose] noncomputable def packFrom (l : List V2) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun r => Nat.shiftLeft r (nat_lit 16384))
    (fun v _ ih r => Nat.lor (Nat.shiftLeft (v2N v) (Nat.mul (nat_lit 128) r)) (ih (Nat.succ r))) l

@[expose] noncomputable def packOK (M : Nat) (l : List V2) : Bool :=
  andB (Nat.beq (packFrom l (nat_lit 0)) (Nat.lor M (Nat.shiftLeft (nat_lit 112) (nat_lit 16384))))
    (List.rec (motive := fun _ => Bool) true
      (fun v _ ih => andB (Nat.blt (v2N v) (Nat.shiftLeft (nat_lit 1) (nat_lit 112))) ih) l)

end CFSG.KC.J4Q

end
