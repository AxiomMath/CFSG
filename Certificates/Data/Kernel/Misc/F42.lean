module

public import Certificates.Data.Kernel.Misc.Base

public section

namespace CFSG.KC.Misc.F42

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc

@[expose] noncomputable def planeMask : Nat := Nat.sub (Nat.shiftLeft 1 2704) 1

@[expose] noncomputable def rowF : Nat := Nat.sub (Nat.shiftLeft 1 52) 1

@[expose] noncomputable def rowR : Nat := Nat.div planeMask rowF

@[expose] noncomputable def addS (ap am bp bm : Nat) : Nat :=
  letN (Nat.lor ap am) fun a0 => letN (Nat.lor bp bm) fun b0 =>
  Nat.lor (Nat.lor (Nat.lor (Nat.xor ap (Nat.land ap b0)) (Nat.xor bp (Nat.land bp a0)))
      (Nat.land am bm))
    (Nat.shiftLeft (Nat.lor (Nat.lor (Nat.xor am (Nat.land am b0)) (Nat.xor bm (Nat.land bm a0)))
      (Nat.land ap bp)) 2704)

@[expose] noncomputable def mulS (A B : Nat) : Nat :=
  letN A fun A => letN B fun B => letN planeMask fun M => letN rowR fun R => letN rowF fun F =>
  letN (Nat.land A M) fun Ap => letN (Nat.shiftRight A 2704) fun Am =>
  letN (Nat.land B M) fun Bp => letN (Nat.shiftRight B 2704) fun Bm =>
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun k acc => letN acc fun acc =>
    letN (Nat.mul (Nat.land (Nat.shiftRight Ap k) R) F) fun Sp =>
    letN (Nat.mul (Nat.land (Nat.shiftRight Am k) R) F) fun Sm =>
    letN (Nat.mul (Nat.land (Nat.shiftRight Bp (Nat.mul 52 k)) F) R) fun Rp =>
    letN (Nat.mul (Nat.land (Nat.shiftRight Bm (Nat.mul 52 k)) F) R) fun Rm =>
    addS (Nat.land acc M) (Nat.shiftRight acc 2704)
      (Nat.lor (Nat.land Sp Rp) (Nat.land Sm Rm)) (Nat.lor (Nat.land Sp Rm) (Nat.land Sm Rp)))
    52

@[expose] noncomputable def idS : Nat :=
  Nat.div (Nat.sub (Nat.shiftLeft 1 2756) 1) (Nat.sub (Nat.shiftLeft 1 53) 1)

@[expose] noncomputable def mulI (A B : Nat) : Nat :=
  letN A fun A => letN B fun B => letN idS fun E =>
    Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (mulS A B) B (Nat.beq A E))
      A (Nat.beq B E)

@[expose] noncomputable def negS (X : Nat) : Nat :=
  letN X fun X => Nat.lor (Nat.shiftRight X 2704) (Nat.shiftLeft (Nat.land X planeMask) 2704)

@[expose] noncomputable def wfS (X : Nat) : Bool :=
  letB X fun X => andB (Nat.blt X (Nat.shiftLeft 1 5408))
    (Nat.beq (Nat.land (Nat.land X planeMask) (Nat.shiftRight X 2704)) 0)

@[expose] noncomputable def eqPMS (X Y : Nat) : Bool :=
  letB X fun X => letB Y fun Y => orB (Nat.beq X Y) (Nat.beq X (negS Y))

@[expose] noncomputable def commS (X Y : Nat) : Bool := Nat.beq (mulI X Y) (mulI Y X)

@[expose] noncomputable def wsK (c : Nat) : Bool :=
  orB (Nat.beq c 32) (orB (Nat.beq c 9) (orB (Nat.beq c 10) (orB (Nat.beq c 13)
    (orB (Nat.beq c 11) (Nat.beq c 12)))))

@[expose] noncomputable def afterNL (cs : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil
    (fun c t ih => Bool.rec (motive := fun _ => List Nat) ih t (Nat.beq c 10)) cs

@[expose] noncomputable def entryK (c : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) 0 (Nat.sub c 48) (andB (Nat.ble 48 c) (Nat.ble c 57))

@[expose] noncomputable def decodeK (cs : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun c _ ih i acc => Bool.rec (motive := fun _ => Nat)
      (letN (Nat.mod (entryK c) 3) fun v => ih (Nat.succ i) (Bool.rec (motive := fun _ => Nat)
        acc (Nat.lor acc (Nat.shiftLeft 1
          (Bool.rec (motive := fun _ => Nat) i (Nat.add i 2704) (Nat.beq v 2))))
        (andB (Nat.blt 0 v) (Nat.blt i 2704))))
      (ih i acc) (wsK c)) (afterNL cs) 0 0

@[expose] noncomputable def fmtK (cs : List Nat) : Bool :=
  (List.rec (motive := fun _ => Nat → Bool) (fun st => notB (Nat.beq st 1))
    (fun c _ ih st => Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) false
          (andB (Nat.beq st 0) (ih 1)) (Nat.beq c 45))
        (ih 2) (andB (Nat.ble 48 c) (Nat.ble c 57)))
      (andB (notB (Nat.beq st 1)) (ih 0)) (orB (Nat.beq c 32) (Nat.beq c 10)))) cs 0

@[expose] noncomputable def intsK (cs : List Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat)
    (fun st => Bool.rec (motive := fun _ => List Nat) List.nil
      [codeOf st] (Nat.ble 2 st))
    (fun c _ ih st => Bool.rec (motive := fun _ => List Nat)
      (Bool.rec (motive := fun _ => List Nat) (ih 1)
        (letLN (Nat.add (Nat.mul 10 (valOf st)) (Nat.sub c 48)) fun v =>
          ih (Nat.add 2 (Nat.add (Nat.mul 2 v) (signOf st))))
        (andB (Nat.ble 48 c) (Nat.ble c 57)))
      (Bool.rec (motive := fun _ => List Nat) (ih 0) (List.cons (codeOf st) (ih 0)) (Nat.ble 2 st))
      (orB (Nat.beq c 32) (Nat.beq c 10))) cs 0
where
  valOf (st : Nat) : Nat :=
    Bool.rec (motive := fun _ => Nat) 0 (Nat.div (Nat.sub st 2) 2) (Nat.ble 2 st)
  signOf (st : Nat) : Nat :=
    Bool.rec (motive := fun _ => Nat) (Nat.mod (Nat.sub st 2) 2) 1 (Nat.beq st 1)
  codeOf (st : Nat) : Nat :=
    Bool.rec (motive := fun _ => Nat) (Nat.mul 2 (valOf st))
      (Nat.add (Nat.mul 2 (Nat.sub (valOf st) 1)) 1)
      (andB (Nat.beq (Nat.mod (Nat.sub st 2) 2) 1) (Nat.blt 0 (valOf st)))

@[expose] noncomputable def nthV (l : List Nat) (i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun x _ ih i => Nat.rec (motive := fun _ => Nat) x (fun j _ => ih j) i) l i

@[expose] noncomputable def refK (F I : List Nat) (c : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nthV I (Nat.div c 2)) (nthV F (Nat.div c 2))
    (Nat.beq (Nat.mod c 2) 0)

@[expose] noncomputable def refOK (F I : List Nat) (n c : Nat) : Bool :=
  andB (Nat.blt (Nat.div c 2) n) (impB (Nat.beq (Nat.mod c 2) 1)
    (Nat.beq (mulS (nthV F (Nat.div c 2)) (nthV I (Nat.div c 2))) idS))

@[expose] noncomputable def insK (F I R : List Nat) (t : Nat) : Bool :=
  letB (nthV R (Nat.mul 2 t)) fun cx => letB (nthV R (Nat.succ (Nat.mul 2 t))) fun cy =>
  andB (refOK F I (Nat.add t 2) cx) (andB (refOK F I (Nat.add t 2) cy)
    (Nat.beq (mulS (refK F I cx) (refK F I cy)) (nthV F (Nat.add t 2))))

@[expose] noncomputable def insChunk (F I R : List Nat) (m lo n : Nat) : Bool :=
  allN n fun d => impB (Nat.blt (Nat.add lo d) m) (insK F I R (Nat.add lo d))

@[expose] noncomputable def startK (pA pB : List Nat) (F I : List Nat) : Bool :=
  letB (decodeK pA) fun A => letB (decodeK pB) fun B =>
  andB (Nat.beq (nthV F 0) A) (andB (Nat.beq (nthV F 1) B) (andB (Nat.beq (mulS A A) idS)
    (andB (Nat.beq (mulS B (mulS B B)) idS) (andB (Nat.beq (mulS A (nthV I 0)) idS)
      (Nat.beq (mulS B (nthV I 1)) idS)))))

@[expose] noncomputable def offR : Nat := nat_lit 8521760

@[expose] noncomputable def codeR (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun x _ ih t => Nat.add (Nat.shiftLeft x (Nat.mul 6 t)) (ih (Nat.succ t))) l 0

@[expose] noncomputable def idxR (RC : List Nat) (v : Nat) : Nat :=
  letN v fun v => List.rec (motive := fun _ => Nat → Nat) (fun _ => 48)
    (fun x _ ih i => Bool.rec (motive := fun _ => Nat) (ih (Nat.succ i)) i (Nat.beq x v)) RC 0

@[expose] noncomputable def rootsK (RL : List (List Nat)) (RC : List Nat) : Bool :=
  andB (Nat.beq (lenN RC) 48) <| andB (Nat.beq (List.rec (motive := fun _ => Nat) 0
      (fun _ _ ih => Nat.succ ih) RL) 48) <|
    allN 48 fun k => letB (nthV RC k) fun c => andB (Nat.beq c (codeR (nthLLR RL k)))
      (andB (Nat.beq (lenN (nthLLR RL k)) 4) (allL (nthLLR RL k) fun x =>
        andB (Nat.ble 24 x) (Nat.ble x 40)))
where
  nthLLR (L : List (List Nat)) (k : Nat) : List Nat :=
    List.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
      (fun x _ ih i => Nat.rec (motive := fun _ => List Nat) x (fun j _ => ih j) i) L k

@[expose] noncomputable def factorK (LF RC : List Nat) (c : Bool) (v : Nat) : Nat :=
  letN (idxR RC v) fun k => Bool.rec (motive := fun _ => Nat) idS (nthV LF k)
    (andB c (Nat.blt k 48))

@[expose] noncomputable def commArrK (LF LI : List Nat) (i j : Nat) : Nat :=
  mulS (mulS (mulS (nthV LF i) (nthV LF j)) (nthV LI i)) (nthV LI j)

@[expose] noncomputable def factorsK (LF RC : List Nat) (i j : Nat) (k : Nat → Nat → Nat → Bool) :
    Bool :=
  letB (nthV RC i) fun a => letB (nthV RC j) fun b =>
  letB (factorK LF RC (Nat.blt 47 (idxR RC (Nat.sub (Nat.add b offR) a)))
    (Nat.sub (Nat.add a b) offR)) fun f11 =>
  letB (factorK LF RC true (Nat.sub (Nat.add a (Nat.add b b)) (Nat.add offR offR))) fun f12 =>
  letB (factorK LF RC true (Nat.sub (Nat.add (Nat.add a a) b) (Nat.add offR offR))) fun f21 =>
    k f11 f12 f21

@[expose] noncomputable def pairK (LF LI RC : List Nat) (i j : Nat) : Bool :=
  factorsK LF RC i j fun f11 f12 f21 =>
    andB (eqPMS (commArrK LF LI i j) (mulI (mulI f11 f12) f21))
      (andB (commS f11 f12) (andB (commS f11 f21) (commS f12 f21)))

@[expose] noncomputable def oppK (RC : List Nat) (i j : Nat) : Bool :=
  Nat.beq (Nat.add (nthV RC i) (nthV RC j)) (Nat.add offR offR)

@[expose] noncomputable def pairsChunk (LF LI RC : List Nat) (lo n : Nat) : Bool :=
  allN n fun d => letB (Nat.add lo d) fun i => impB (Nat.blt i 48)
    (allN 48 fun j => orB (Nat.beq i j) (orB (oppK RC i j) (pairK LF LI RC i j)))

@[expose] noncomputable def liftK (LF LI : List Nat) (k : Nat) : Bool :=
  letB (nthV LF k) fun X => letB (nthV LI k) fun Y =>
  andB (wfS X) (andB (wfS Y) (andB (Nat.beq (mulS X Y) idS) (andB (Nat.beq (mulS Y X) idS)
    (eqPMS (mulS X X) idS))))

@[expose] noncomputable def wordK (LF LI RC : List Nat) (k p q : Nat) : Bool :=
  letB (nthV RC p) fun a => letB (nthV RC q) fun b =>
  andB (Nat.blt p 48) <| andB (Nat.blt q 48) <| andB (notB (Nat.beq p q)) <|
  andB (notB (Nat.beq (Nat.add a b) (Nat.add offR offR))) <|
  andB (Nat.beq (Nat.sub (Nat.add a b) offR) (nthV RC k)) <|
  andB (Nat.beq (idxR RC (Nat.sub (Nat.add a (Nat.add b b)) (Nat.add offR offR))) 48) <|
  andB (Nat.beq (idxR RC (Nat.sub (Nat.add (Nat.add a a) b) (Nat.add offR offR))) 48) <|
  andB (Nat.beq (idxR RC (Nat.sub (Nat.add b offR) a)) 48) <|
    Nat.beq (commArrK LF LI p q) (nthV LF k)

@[expose] noncomputable def negK (LF LI RC : List Nat) (i j : Nat) : Bool :=
  andB (Nat.blt i 48) <| andB (Nat.blt j 48) <| andB (notB (Nat.beq i j)) <|
  andB (notB (oppK RC i j)) <|
    factorsK LF RC i j fun f11 f12 f21 =>
      Nat.beq (commArrK LF LI i j) (negS (mulI (mulI f11 f12) f21))

@[expose] noncomputable def liftsK (F I LR LF LI : List Nat) (n : Nat) : Bool :=
  andB (Nat.beq (lenN LR) 48) <|
    allN 48 fun k => letB (nthV LR k) fun c => letB (Nat.xor c 1) fun c' =>
      andB (refOK F I n c) (andB (refOK F I n c')
        (andB (Nat.beq (nthV LF k) (refK F I c)) (Nat.beq (nthV LI k) (refK F I c'))))

end CFSG.KC.Misc.F42

end
