module

public import Certificates.Data.Kernel.OpsLayMcert

public section

namespace CFSG.KC.NC2L

open CFSG.KC.LQT CFSG.KC.Ord CFSG.KC.OpsLayK CFSG.SectionRank.Native

structure LiveChunk where
  n : Nat
  prog : List Op
  out : List Nat

@[expose] def padR (c : Lay) (R : List Nat) (n : Nat) : List Nat :=
  R ++ List.replicate (n - R.length) c.ONE

@[expose] noncomputable def liveL (c : Lay) (C : LiveChunk) (R S : List Nat) : Bool :=
  runC c C.prog (padR c R C.n) fun R' => eqL (C.out.map (getR c R')) S

@[expose] noncomputable def nfL (c : Lay) (gs : List Nat) (n : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => c.ONE)
    (fun g _ ih n => Bool.rec (motive := fun _ => Nat) (ih (Nat.div n 2))
      (Bool.rec (motive := fun _ => Nat) (c.mul g (ih (Nat.div n 2))) g (Nat.beq (Nat.div n 2) 0))
      (Nat.beq (Nat.mod n 2) 1)) gs n

inductive BT where
  | leaf (v : Nat)
  | node (l r : BT)

@[expose] noncomputable def BT.get (T : BT) : Nat → Nat :=
  BT.rec (motive := fun _ => Nat → Nat) (fun v _ => v)
    (fun _ _ il ir n => Bool.rec (motive := fun _ => Nat) (il (Nat.div n 2)) (ir (Nat.div n 2))
      (Nat.beq (Nat.mod n 2) 1)) T

@[expose] noncomputable def mapV (c : Lay) (M : Nat) (us : List Nat) : (List Nat → Bool) → Bool :=
  List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun k => k [])
    (fun u _ ih k => strictB (c.vec u M) fun v => ih fun vs => k (v :: vs)) us

@[expose] noncomputable def keyOf (B : Nat) (vs : List Nat) (k : Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun acc => k acc)
    (fun v _ ih acc => strictB (Nat.add (Nat.mul acc B) v) ih) vs (nat_lit 0)

@[expose] noncomputable def vecsTree (c : Lay) (post : List Nat → (Nat → Bool) → Bool)
    (gs : List Nat) : List Nat → (BT → Bool) → Bool :=
  List.rec (motive := fun _ => List Nat → (BT → Bool) → Bool)
    (fun us k => post us fun v => k (BT.leaf v))
    (fun g _ ih us k => ih us fun l => mapV c g us fun us' => ih us' fun r => k (BT.node l r)) gs

@[expose] noncomputable def dropLt (f : Nat → Nat) (v : Nat) (σ : List Nat) :
    (List Nat → Bool) → Bool :=
  List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun k => k [])
    (fun h t ih k => strictB (f h) fun w => Bool.rec (motive := fun _ => Bool) (k (h :: t)) (ih k)
      (Nat.blt w v)) σ

@[expose] noncomputable def memB (k : Nat) (ns : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun h _ ih => orB (Nat.beq h k) ih) ns

@[expose] noncomputable def headOK (f : Nat → Nat) (v : Nat) (ok : Bool) (σ : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun h _ _ => orB (notB (Nat.beq (f h) v)) ok) σ

@[expose] noncomputable def mergeRun (N : Nat) (fc fs : Nat → Nat) (ns : List Nat) (τ : List Nat) :
    Nat → Nat → List Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → List Nat → Bool)
    (fun _ mask _ => Nat.beq mask (Nat.sub (Nat.shiftLeft (nat_lit 1) N) (nat_lit 1)))
    (fun k _ ih lo mask σ => strictB (fc k) fun v =>
      andB (Nat.blt k N) (andB (Nat.beq (Nat.land mask (Nat.shiftLeft (nat_lit 1) k)) (nat_lit 0))
        (andB (Nat.ble lo v) (dropLt fs v σ fun σ' =>
          andB (headOK fs v (memB k ns) σ')
            (strictB (Nat.lor mask (Nat.shiftLeft (nat_lit 1) k)) fun m1 => ih v m1 σ')))))
    τ

structure NC2LData where
  a : Nat
  tests : List Nat
  oddExp : Nat
  extra : List Nat
  sq : List Nat
  cj : List (List Nat)
  sig : List Nat
  sigma : List Nat
  tau : List Nat
  pairs : List (Nat × Nat)

@[expose] noncomputable def movesL (c : Lay) (tests : List Nat) (M : Nat) : Bool :=
  tests.any fun k => !Nat.beq (c.vec (c.unit k) M) (c.unit k)

@[expose] def primeB (q : Nat) : Bool :=
  Nat.ble 2 q && (List.range q).all fun k => Nat.blt k 2 || !Nat.beq (Nat.mod q k) 0

@[expose] noncomputable def pcL (c : Lay) (a : Nat) (gs sq : List Nat) (cj : List (List Nat)) :
    Bool :=
  Nat.beq sq.length a && Nat.beq cj.length a &&
    (List.range a).all fun i =>
      Nat.blt (sq.getD i 0) (Nat.pow 2 a) && Nat.beq (Nat.mod (sq.getD i 0) (Nat.pow 2 (i + 1))) 0 &&
        Nat.beq (c.mul (getR c gs i) (getR c gs i)) (nfL c gs (sq.getD i 0)) &&
        Nat.beq (cj.getD i []).length (a - (i + 1)) &&
        (List.range (cj.getD i []).length).all fun t =>
          Nat.blt ((cj.getD i []).getD t 0) (Nat.pow 2 a) &&
            Nat.beq (Nat.mod ((cj.getD i []).getD t 0) (Nat.pow 2 (i + 1))) 0 &&
            Nat.beq (c.mul (getR c gs (i + 1 + t)) (getR c gs i))
              (c.mul (getR c gs i) (nfL c gs ((cj.getD i []).getD t 0)))

@[expose] noncomputable def sigL (c : Lay) (D : NC2LData) (G Gi : Nat) (gs : List Nat) : Bool :=
  andB (D.sig.all fun k => Nat.blt k c.d)
    (vecsTree c (keyOf (Nat.shiftLeft 1 c.S)) gs (D.sig.map c.unit) fun sT =>
      mapV c G (D.sig.map c.unit) fun u0 =>
      vecsTree c (fun us k => mapV c Gi us fun ws => keyOf (Nat.shiftLeft 1 c.S) ws k) gs u0
        fun cT =>
      andB (sortRun (Nat.pow 2 D.a) sT.get D.sigma 0 0)
        (mergeRun (Nat.pow 2 D.a) cT.get sT.get (D.pairs.map Prod.fst) D.tau 0 0 D.sigma))

@[expose] noncomputable def nc2L (c : Lay) (O : List Nat) (D : NC2LData) : Bool :=
  Nat.beq O.length (4 + D.extra.length + D.a) && D.tests.all (fun k => Nat.blt k c.d) &&
    Nat.beq (c.mul (getR c O 0) (getR c O 0)) c.ONE && movesL c D.tests (getR c O 0) &&
    commK c (getR c O 1) (getR c O 0) && commK c (getR c O 3) (getR c O 0) &&
    Nat.beq (c.mul (getR c O 1) (getR c O 2)) c.ONE &&
    Nat.beq (Nat.mod D.oddExp 2) 1 && Nat.blt D.oddExp 65536 &&
    Nat.beq (powK c (getR c O 3) D.oddExp) c.ONE && movesL c D.tests (getR c O 3) &&
    (List.range D.extra.length).all (fun i =>
      primeB (D.extra.getD i 0) && Nat.blt (D.extra.getD i 0) 65536 &&
        commK c (getR c O (4 + i)) (getR c O 0) &&
        Nat.beq (powK c (getR c O (4 + i)) (D.extra.getD i 0)) c.ONE &&
        movesL c D.tests (getR c O (4 + i))) &&
    (O.drop (4 + D.extra.length)).all (fun g => commK c g (getR c O 0)) &&
    pcL c D.a (O.drop (4 + D.extra.length)) D.sq D.cj &&
    D.pairs.all (fun m => Nat.blt m.1 (Nat.pow 2 D.a) &&
      commK c (getR c O 3)
        (c.mul (c.mul (getR c O 1) (nfL c (O.drop (4 + D.extra.length)) m.1)) (getR c O 2))) &&
    sigL c D (getR c O 1) (getR c O 2) (O.drop (4 + D.extra.length))

end CFSG.KC.NC2L

end
