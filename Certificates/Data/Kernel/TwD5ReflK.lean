module

public section

namespace CFSG.KC.TwD5R

@[expose] noncomputable def andB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) false b a

@[expose] noncomputable def orB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) b true a

@[expose] noncomputable def notB (a : Bool) : Bool := Bool.rec (motive := fun _ => Bool) true false a

@[expose] noncomputable def letN {α : Type} (y : Nat) (k : Nat → α) : α := k y

@[expose] noncomputable def selN (c : Bool) (t e : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) e t c

@[expose] noncomputable def dg (x j : Nat) : Nat := Nat.mod (Nat.div x (Nat.pow 3 j)) 3

@[expose] noncomputable def dot (v f : Nat) : Nat :=
  Nat.mod (Nat.add (Nat.add (Nat.add (Nat.mul (dg v 0) (dg f 0)) (Nat.mul (dg v 1) (dg f 1)))
    (Nat.add (Nat.mul (dg v 2) (dg f 2)) (Nat.mul (dg v 3) (dg f 3))))
    (Nat.add (Nat.mul (dg v 4) (dg f 4)) (Nat.mul (dg v 5) (dg f 5)))) 3

@[expose] noncomputable def negV (x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun j ih => Nat.add ih (Nat.mul (Nat.mod (Nat.mul 2 (dg x j)) 3) (Nat.pow 3 j))) 6

@[expose] noncomputable def lowD (x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun y => Nat.mod y 3)
    (fun _ ih y => Bool.rec (motive := fun _ => Nat) (Nat.mod y 3) (ih (Nat.div y 3))
      (Nat.beq (Nat.mod y 3) 0)) 6 x

@[expose] noncomputable def canon (x : Nat) : Bool := Nat.beq (lowD x) 1

@[expose] noncomputable def canonKey (v f : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (Nat.add (Nat.mul (negV v) 729) (negV f))
    (Nat.add (Nat.mul v 729) f) (canon v)

@[expose] noncomputable def keyOK (key : Nat) : Bool :=
  andB (Nat.blt key 531441) (andB (canon (Nat.div key 729))
    (Nat.beq (dot (Nat.div key 729) (Nat.mod key 729)) 1))

@[expose] noncomputable def lane (hc j : Nat) : Nat := Nat.land (Nat.shiftRight hc (Nat.mul 3 j)) 7

@[expose] noncomputable def sbit (hc j : Nat) : Nat :=
  Nat.land (Nat.shiftRight hc (Nat.add 18 j)) 1

@[expose] noncomputable def PAR64 : Nat := 7608434000728254870

@[expose] noncomputable def validH (fx : Bool) (hc : Nat) : Bool :=
  andB (Nat.blt hc 16777216) (andB (Nat.beq (lane hc 0) 0)
    (andB (Nat.beq (Nat.lor (Nat.lor (Nat.lor (Nat.shiftLeft 1 (lane hc 0))
        (Nat.shiftLeft 1 (lane hc 1))) (Nat.lor (Nat.shiftLeft 1 (lane hc 2))
        (Nat.shiftLeft 1 (lane hc 3)))) (Nat.lor (Nat.shiftLeft 1 (lane hc 4))
        (Nat.shiftLeft 1 (lane hc 5)))) 63)
      (andB (Nat.beq (Nat.land (Nat.shiftRight PAR64 (Nat.shiftRight hc 18)) 1) 0)
        (orB (notB fx) (Nat.beq (sbit hc 0) 0)))))

@[expose] noncomputable def term (hc x j : Nat) : Nat :=
  Nat.mul (Nat.mod (Nat.mul (dg x j) (Nat.add 1 (sbit hc j))) 3) (Nat.pow 3 (lane hc j))

@[expose] noncomputable def act (hc x : Nat) : Nat :=
  Nat.add (Nat.add (Nat.add (term hc x 0) (term hc x 1)) (Nat.add (term hc x 2) (term hc x 3)))
    (Nat.add (term hc x 4) (term hc x 5))

@[expose] noncomputable def reflV (key x : Nat) : Nat :=
  letN (dot x (Nat.mod key 729)) fun t => letN (Nat.div key 729) fun v =>
    Nat.rec (motive := fun _ => Nat) 0
      (fun j ih => Nat.add ih (Nat.mul (Nat.mod (Nat.add (dg x j) (Nat.mul t (dg v j))) 3)
        (Nat.pow 3 j))) 6

@[expose] noncomputable def uk (c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 7
    (fun k ih => selN (orB (Nat.beq c (Nat.pow 3 k)) (Nat.beq c (Nat.mul 2 (Nat.pow 3 k)))) k ih) 6

@[expose] noncomputable def us (c : Nat) : Nat :=
  selN (Nat.beq c (Nat.mul 2 (Nat.pow 3 (uk c)))) 1 0

@[expose] noncomputable def colsCode (col : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun j ih => letN (col j) fun c => Nat.add ih
      (Nat.add (Nat.shiftLeft (uk c) (Nat.mul 3 j)) (Nat.shiftLeft (us c) (Nat.add 18 j)))) 6

@[expose] noncomputable def inHCols (fx : Bool) (col : Nat → Nat) : Bool := validH fx (colsCode col)

@[expose] noncomputable def getN (l : List Nat) (i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun x _ ih i => Nat.rec (motive := fun _ => Nat) x (fun k _ => ih k) i) l i

@[expose] noncomputable def eqL (l₁ l₂ : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun l => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) l)
    (fun a _ ih l => List.rec (motive := fun _ => Bool) false (fun b t _ => andB (Nat.beq a b) (ih t)) l)
    l₁ l₂

@[expose] noncomputable def fstL {β : Type} (l : List (Nat × β)) : List Nat :=
  List.rec (motive := fun _ => List Nat) []
    (fun e _ ih => List.cons (Prod.rec (motive := fun _ => Nat) (fun k _ => k) e) ih) l

@[expose] noncomputable def lenN {α : Type} (l : List α) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => Nat.succ ih) l

@[expose] noncomputable def allL {α : Type} (l : List α) (p : α → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ ih => andB (p a) ih) l

@[expose] noncomputable def applyL (gens refls : List Nat) (g x : Nat) : Nat :=
  letN (lenN gens) fun ng =>
    Bool.rec (motive := fun _ => Nat) (reflV (getN refls (Nat.sub g ng)) x) (act (getN gens g) x)
      (Nat.blt g ng)

@[expose] noncomputable def applyW (gens refls : List Nat) (w : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) x (fun g _ ih => applyL gens refls g ih) w

@[expose] noncomputable def badW (fx : Bool) (gens refls : List Nat) (nl : Nat) (w : List Nat) :
    Bool :=
  andB (allL w fun g => Nat.blt g nl)
    (andB (Nat.blt (applyW gens refls w 1) 3)
      (notB (inHCols fx fun j => applyW gens refls w (Nat.pow 3 j))))

@[expose] noncomputable def reflInH (fx : Bool) (key : Nat) : Bool :=
  inHCols fx fun j => reflV key (Nat.pow 3 j)

@[expose] noncomputable def packTab (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun k _ ih => Nat.lor k (Nat.shiftLeft ih 20)) l

@[expose] noncomputable def repAt (repTab r : Nat) : Nat :=
  Nat.land (Nat.shiftRight repTab (Nat.mul 20 r)) 1048575

@[expose] noncomputable def recOK (fx : Bool) (repTab nrep v f rec : Nat) : Bool :=
  letN (Nat.land rec 511) fun r => letN (Nat.shiftRight rec 9) fun hc =>
    andB (Nat.blt r nrep) (andB (validH fx hc)
      (Nat.beq (canonKey (act hc v) (act hc f)) (repAt repTab r)))

@[expose] noncomputable def stepF (fx : Bool) (repTab nrep v f : Nat) (st : Option (List Nat)) :
    Option (List Nat) :=
  Bool.rec (motive := fun _ => Option (List Nat)) st
    (Option.rec (motive := fun _ => Option (List Nat)) none
      (fun l => List.rec (motive := fun _ => Option (List Nat)) none
        (fun rec tl _ => Bool.rec (motive := fun _ => Option (List Nat)) none (some tl)
          (recOK fx repTab nrep v f rec)) l) st)
    (Nat.beq (dot v f) 1)

@[expose] noncomputable def loopF (fx : Bool) (repTab nrep v : Nat) (st : Option (List Nat)) :
    Option (List Nat) :=
  Nat.rec (motive := fun _ => Option (List Nat)) st
    (fun f ih => stepF fx repTab nrep v f ih) 729

@[expose] noncomputable def k1OK (fx : Bool) (repTab nrep lo n : Nat) (recs : List Nat) : Bool :=
  Option.rec (motive := fun _ => Bool) false
    (fun l => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) l)
    (Nat.rec (motive := fun _ => Option (List Nat)) (some recs)
      (fun i ih => letN (Nat.add lo i) fun v =>
        Bool.rec (motive := fun _ => Option (List Nat)) ih (loopF fx repTab nrep v ih) (canon v))
      n)

@[expose] noncomputable def tabOK (reps : List Nat) (repTab nrep : Nat) : Bool :=
  andB (Nat.beq (packTab reps) repTab) (andB (Nat.beq (lenN reps) nrep)
    (andB (Nat.blt nrep 512) (allL reps fun k => Nat.blt k 531441)))

@[expose] noncomputable def repNOK (fx : Bool) (reps : List Nat) : Bool :=
  allL reps fun k => andB (keyOK k) (notB (reflInH fx k))

@[expose] noncomputable def badOK (fx : Bool) (gens : List Nat) (bad : List (Nat × List Nat)) :
    Bool :=
  allL bad fun e => Prod.rec (motive := fun _ => Bool)
    (fun k w => badW fx gens [k] (Nat.succ (lenN gens)) w) e

@[expose] noncomputable def k12OK (fx : Bool) (gens goods : List Nat) (ws : List (List Nat)) :
    Bool :=
  letN (lenN goods) fun m =>
  Option.rec (motive := fun _ => Bool) false
    (fun l => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) l)
    (Nat.rec (motive := fun _ => Option (List (List Nat))) (some ws)
      (fun i ih => letN (Nat.div i m) fun c => letN (Nat.mod i m) fun c2 =>
        Bool.rec (motive := fun _ => Option (List (List Nat)))
          (Option.rec (motive := fun _ => Option (List (List Nat))) none
            (fun l => List.rec (motive := fun _ => Option (List (List Nat))) none
              (fun w tl _ => Bool.rec (motive := fun _ => Option (List (List Nat))) none (some tl)
                (badW fx gens [getN goods c, getN goods c2] (Nat.add (lenN gens) 2) w)) l) ih)
          ih (Nat.beq c c2))
      (Nat.mul m m))

@[expose] noncomputable def incr (l : List (Nat × Nat)) : Bool :=
  Option.rec (motive := fun _ => Bool) false (fun _ => true)
    (List.rec (motive := fun _ => Option Nat) (some 531441)
      (fun e _ ih => Option.rec (motive := fun _ => Option Nat) none
        (fun nx => Prod.rec (motive := fun _ => Option Nat)
          (fun k _ => Bool.rec (motive := fun _ => Option Nat) none (some k) (Nat.blt k nx)) e) ih) l)

@[expose] noncomputable def maskL (l : List (Nat × Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun e _ ih => Prod.rec (motive := fun _ => Nat) (fun k _ => Nat.lor (Nat.shiftLeft 1 k) ih) e) l

@[expose] noncomputable def inM (M k : Nat) : Bool := Nat.blt 0 (Nat.land M (Nat.shiftLeft 1 k))

@[expose] noncomputable def closedAt (gens : List Nat) (M key : Nat) : Bool :=
  letN (Nat.div key 729) fun v => letN (Nat.mod key 729) fun f =>
    allL gens fun g => inM M (canonKey (act g v) (act g f))

@[expose] noncomputable def lhOK (fx : Bool) (gens reps : List Nat) (l : List (Nat × Nat)) : Bool :=
  andB (incr l) (letN (maskL l) fun M =>
    andB (allL reps fun k => inM M k)
      (allL l fun e => Prod.rec (motive := fun _ => Bool)
        (fun k _ => andB (keyOK k) (andB (reflInH fx k) (closedAt gens M k))) e))

@[expose] noncomputable def lgOK (fx : Bool) (gens : List Nat) (gk : Nat) (l : List (Nat × Nat)) :
    Bool :=
  andB (incr l) (letN (maskL l) fun M =>
    andB (inM M gk)
      (allL l fun e => Prod.rec (motive := fun _ => Bool)
        (fun k w => letN (Nat.land w 16777215) fun hc =>
          andB (keyOK k) (andB (validH fx hc)
            (andB (Nat.beq (canonKey (act hc (Nat.div k 729)) (act hc (Nat.mod k 729))) gk)
              (closedAt gens M k)))) e))

@[expose] noncomputable def ALL : Nat := Nat.sub (Nat.shiftLeft 1 729) 1

@[expose] noncomputable def plane (j d : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun x ih => Nat.lor ih (Nat.shiftLeft (selN (Nat.beq (dg x j) d) 1 0) x)) 729

@[expose] noncomputable def planes : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun j ih => Nat.lor ih (Nat.shiftLeft (Nat.lor (plane j 1) (Nat.shiftLeft (plane j 2) 729))
      (Nat.mul 1458 j))) 6

@[expose] noncomputable def laneP (P i : Nat) : Nat := Nat.land (Nat.shiftRight P (Nat.mul 729 i)) ALL

@[expose] noncomputable def add3 (a1 a2 : Nat) (t : Nat × Nat) : Nat × Nat :=
  Prod.rec (motive := fun _ => Nat × Nat) (fun t1 t2 =>
    letN (Nat.xor ALL (Nat.lor t1 t2)) fun t0 => letN (Nat.xor ALL (Nat.lor a1 a2)) fun a0 =>
      (Nat.lor (Nat.lor (Nat.land t0 a1) (Nat.land t1 a0)) (Nat.land t2 a2),
       Nat.lor (Nat.lor (Nat.land t0 a2) (Nat.land t2 a0)) (Nat.land t1 a1))) t

@[expose] noncomputable def zmask (P f : Nat) : Nat :=
  Prod.rec (motive := fun _ => Nat) (fun t1 t2 => Nat.xor ALL (Nat.lor t1 t2))
    (Nat.rec (motive := fun _ => Nat × Nat) (0, 0)
      (fun j ih => letN (dg f j) fun d =>
        Bool.rec (motive := fun _ => Nat × Nat)
          (add3 (laneP P (Nat.add (Nat.mul 2 j) (Nat.sub d 1)))
            (laneP P (Nat.add (Nat.mul 2 j) (Nat.sub 2 d))) ih) ih (Nat.beq d 0)) 6)

@[expose] noncomputable def incC (C : List Nat) (z : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun p _ ih c => List.cons (Nat.xor p c) (ih (Nat.land p c))) C z

@[expose] noncomputable def countL (P : Nat) (l : List (Nat × Nat)) (C : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun C => C)
    (fun e _ ih C => Prod.rec (motive := fun _ => List Nat)
      (fun k _ => ih (incC C (zmask P (Nat.mod k 729)))) e) l C

@[expose] noncomputable def eqE0 (C : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) ALL
    (fun p _ ih => Nat.land ih
      (selN (Nat.beq (Nat.land (Nat.shiftRight p 1) 1) 1) p (Nat.xor ALL p))) C

@[expose] noncomputable def reachM (gens refls : List Nat) (nl : Nat)
    (ow : List (Nat × (Nat × Nat))) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun R => R)
    (fun e _ ih R => Prod.rec (motive := fun _ => Nat) (fun x yg => Prod.rec (motive := fun _ => Nat)
      (fun y g => letN (applyL gens refls g y) fun z =>
        Bool.rec (motive := fun _ => Nat) 0
          (ih (Nat.lor R (Nat.lor (Nat.shiftLeft 1 x) (Nat.shiftLeft 1 (negV x)))))
          (andB (inM R y) (andB (Nat.blt g nl) (andB (Nat.blt x 729)
            (orB (Nat.beq z x) (Nat.beq z (negV x))))))) yg) e) ow 6

@[expose] noncomputable def k3OK (gens : List Nat) (gk : Nat) (lh lg : List (Nat × Nat))
    (ow : List (Nat × (Nat × Nat))) : Bool :=
  andB (Nat.blt (Nat.add (lenN lh) (lenN lg)) 4096)
    (letN planes fun P =>
      letN (eqE0 (countL P lg (countL P lh [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) fun E =>
        letN (reachM gens [gk] (Nat.succ (lenN gens)) ow) fun R =>
          Nat.beq (Nat.land (Nat.land E (Nat.sub ALL 1)) (Nat.xor ALL R)) 0)

@[expose] noncomputable def gensFix : List Nat := [181840, 181448, 178312, 153224, 12736136]

@[expose] noncomputable def gensAll : List Nat :=
  [181840, 181448, 178312, 153224, 12736136, 968328]

@[expose] noncomputable def goodsFix : List Nat := [236845, 265354, 442258]

@[expose] noncomputable def goodsAll : List Nat := [355268, 236845, 265354, 442258]

@[expose] noncomputable def repsOK (goods reps repsH : List Nat) (repsB : List (Nat × List Nat)) :
    Bool :=
  eqL reps (List.append goods (List.append repsH (fstL repsB)))

end CFSG.KC.TwD5R
