module

public import CFSG.Certificates.Kernel.Common.Loop
public import CFSG.Certificates.Kernel.Common.LceS
public import Certificates.Data.Kernel.Spor.Fi24NetPt

public section

namespace CFSG.KC.Fi24Pc

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.Fi24Net CFSG.KC.Fi24NetPt

@[expose] noncomputable def ex (u k : Nat) : Nat := fld(u, Nat.shiftLeft k (nat_lit 1), nat_lit 3)

@[expose] noncomputable def nwOK (u : Nat) : Bool :=
  andB (Nat.blt u (nat_lit 4294967296))
    (Nat.beq (Nat.land (Nat.land u (Nat.shiftRight u (nat_lit 1))) (nat_lit 1431655765)) (nat_lit 0))

@[expose] noncomputable def gw (i : Nat) : Nat := Nat.shiftLeft (nat_lit 1) (Nat.shiftLeft i (nat_lit 1))

@[expose] noncomputable def lowM (i : Nat) : Nat := Nat.sub (gw i) (nat_lit 1)

@[expose] noncomputable def f32 (T k : Nat) : Nat :=
  fld(T, Nat.shiftLeft k (nat_lit 5), nat_lit 4294967295)

@[expose] noncomputable def nth (l : List Nat) (i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun a _ ih i => Nat.rec (motive := fun _ => Nat) a (fun k _ => ih k) i) l i

@[expose] noncomputable def nthL (l : List (List Nat)) (i : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun a _ ih i => Nat.rec (motive := fun _ => List Nat) a (fun k _ => ih k) i) l i

@[expose] noncomputable def nwL (u : Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) List.nil
    (fun j ih => (fun k => (fun e =>
      Bool.rec (motive := fun _ => List Nat)
        (Bool.rec (motive := fun _ => List Nat) (List.cons (Nat.shiftLeft k (nat_lit 1))
          (List.cons (Nat.shiftLeft k (nat_lit 1)) ih))
          (List.cons (Nat.shiftLeft k (nat_lit 1)) ih) (Nat.beq e (nat_lit 1)))
        ih (Nat.beq e (nat_lit 0))) (ex u k)) (Nat.sub (nat_lit 15) j)) (nat_lit 16)

@[expose] def cb : List Nat := [0, 305530, 5604, 221549, 266275, 186844]

@[expose] noncomputable def apP (f : Nat → Nat → Nat) (w : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun l _ ih x => strictN (ih x) (fun y => f l y)) w x

@[expose] noncomputable def eqP (f : Nat → Nat → Nat) (B u v : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun b _ ih => bAnd(Nat.beq (apP f u b) (apP f v b), ih)) B

@[expose] noncomputable def walkP (W : Nat → Nat → Nat) (w : List Nat) (v : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun l _ ih x => strictN (planeL W l x) ih) w v

@[expose] noncomputable def commL (d : Nat) : List Nat :=
  (fun a b => [Nat.add (Nat.shiftLeft a 1) 1, Nat.add (Nat.shiftLeft b 1) 1, Nat.shiftLeft a 1,
    Nat.shiftLeft b 1]) (Nat.land d (nat_lit 255)) (Nat.shiftRight d (nat_lit 8))

@[expose] noncomputable def genW (words : List (List Nat)) (defs : List Nat) (j : Nat) : List Nat :=
  Bool.rec (motive := fun _ => List Nat) (commL (nth defs (Nat.sub j (nat_lit 4)))) (nthL words j)
    (Nat.blt j (nat_lit 4))

@[expose] noncomputable def pcwOK (NW XW : Nat → Nat → Nat) (words : List (List Nat)) (defs : List Nat)
    (j k : Nat) : Bool :=
  letB (tpl k) (fun v => Nat.beq
    (Bool.rec (motive := fun _ => Nat) (walkP XW (genW words defs j) v) (walkP NW (genW words defs j) v)
      (Nat.blt j (nat_lit 4)))
    (netF (XW j) v))

@[expose] noncomputable def relOK (f : Nat → Nat → Nat) (PW CJ j : Nat) : Bool :=
  bAnd(andB (andB (nwOK (f32 PW j)) (Nat.beq (Nat.land (f32 PW j) (lowM (Nat.add j 1))) (nat_lit 0)))
      (eqP f cb [Nat.shiftLeft j 1, Nat.shiftLeft j 1, Nat.shiftLeft j 1] (nwL (f32 PW j))),
    Nat.rec (motive := fun _ => Bool) true
      (fun k ih => bAnd(bIf(Nat.blt j k,
        letB (f32 CJ (Nat.add (Nat.shiftLeft j 4) k)) (fun c =>
          andB (andB (nwOK c) (Nat.beq (Nat.land c (lowM (Nat.add k 1))) (gw k)))
            (eqP f cb [Nat.add (Nat.shiftLeft j 1) 1, Nat.shiftLeft k 1, Nat.shiftLeft j 1] (nwL c))),
        true), ih)) (nat_lit 16))

@[expose] noncomputable def opt (OP a : Nat) : Nat := fld(OP, Nat.mul (nat_lit 19) a, nat_lit 524287)

@[expose] noncomputable def tb (TB k e a : Nat) : Nat :=
  fld(TB, Nat.mul (nat_lit 10) (Nat.add (Nat.mul (nat_lit 729)
    (Nat.sub (Nat.add (Nat.shiftLeft k (nat_lit 1)) e) (nat_lit 1))) a), nat_lit 1023)

@[expose] noncomputable def evO (TB u a : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) a
    (fun j ih => strictN ih (fun b => (fun k => (fun e => nIf(Nat.beq e (nat_lit 0), b, tb TB k e b))
      (ex u k)) (Nat.sub (nat_lit 15) j))) (nat_lit 16)

@[expose] noncomputable def evW (TB : Nat) (ws : List Nat) (a : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun a => a)
    (fun w _ ih a => strictN (ih a) (fun b => evO TB w b)) ws a

@[expose] noncomputable def eqO (TB : Nat) (B l₁ l₂ : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun b _ ih => bAnd(Nat.beq (evW TB l₁ b) (evW TB l₂ b), ih)) B

@[expose] noncomputable def oOK (OP : Nat) : Bool :=
  andB (Nat.blt (opt OP (nat_lit 728)) (nat_lit 306936))
    (allBelow (nat_lit 728) (nat_lit 12) (fun a => Nat.blt (opt OP a) (opt OP (Nat.add a 1))))

@[expose] noncomputable def tabOK (XW : Nat → Nat → Nat) (OP TB k a : Nat) : Bool :=
  letB (tb TB k (nat_lit 1) a) (fun b =>
    bAnd(Nat.blt b (nat_lit 729), bAnd(Nat.beq (letN XW (Nat.shiftLeft k 1) (opt OP a)) (opt OP b),
      Nat.beq (tb TB k (nat_lit 2) a) (tb TB k (nat_lit 1) b))))

@[expose] noncomputable def lenL (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) l

@[expose] noncomputable def orbStep (TB : Nat) (gs : List Nat) (b0 r S : Nat) : Nat :=
  (fun a pa h m M =>
    nIf(bIf(Nat.beq m (nat_lit 0), Nat.beq a b0,
        bAnd(Nat.testBit M pa, bAnd(Nat.blt h (lenL gs), Nat.beq (evO TB (nth gs h) pa) a))),
      nIf(bAnd(Nat.blt a (nat_lit 729), notB (Nat.testBit M a)),
        Nat.add (Nat.add m (nat_lit 1)) (Nat.shiftLeft (Nat.lor M (Nat.shiftLeft (nat_lit 1) a)) (nat_lit 20)),
        nat_lit 1048575),
      nat_lit 1048575))
    (Nat.land r (nat_lit 1023)) (fld(r, nat_lit 10, nat_lit 1023)) (Nat.shiftRight r (nat_lit 20))
    (Nat.land S (nat_lit 1048575)) (Nat.shiftRight S (nat_lit 20))

@[expose] noncomputable def fixB (TB g : Nat) (B : List Nat) (n : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun b _ ih n => Nat.rec (motive := fun _ => Bool) true
      (fun m _ => bAnd(Nat.beq (evO TB g b) b, ih m)) n) B n

@[expose] noncomputable def orbRun (TB : Nat) (gs : List Nat) (b0 : Nat) (R : List Nat) (S : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun r _ ih S => strictN (orbStep TB gs b0 r S) ih) R S

@[expose] noncomputable def orbOK (TB : Nat) (B gs R : List Nat) (l : Nat) : Bool :=
  bAnd(List.rec (motive := fun _ => Bool) true
      (fun g _ ih => bAnd(andB (nwOK g) (fixB TB g B l), ih)) gs,
    Nat.beq (Nat.land (orbRun TB gs (nth B l) R (nat_lit 0)) (nat_lit 1048575)) (lenL R))

@[expose] noncomputable def repOK (TB : Nat) (B : List Nat) (i y g : Nat) : Bool :=
  (fun t a b =>
    bIf(Nat.beq t (nat_lit 0),
      bAnd(nwOK a, bAnd(notB (Nat.beq (Nat.land a (lowM i)) (nat_lit 0)), eqO TB B [y, y, y] [a])),
      bIf(Nat.beq t (nat_lit 1),
        bAnd(nwOK a, bAnd(nwOK b, bAnd(Nat.beq (Nat.land b (lowM (Nat.add i 1))) (nat_lit 0),
          eqO TB B [a, y] [y, gw i, a, b]))),
        Nat.beq t (nat_lit 2))))
    (Nat.land g (nat_lit 3)) (fld(g, nat_lit 2, nat_lit 4294967295)) (Nat.shiftRight g (nat_lit 34))

@[expose] noncomputable def kids (i y g : Nat) (rest : List Nat) : List Nat :=
  (fun t => Bool.rec (motive := fun _ => List Nat)
    (Bool.rec (motive := fun _ => List Nat) (List.cons y (List.cons (Nat.add y (gw i))
        (List.cons (Nat.add y (Nat.shiftLeft (gw i) 1)) rest))) (List.cons y rest) (Nat.beq t 1))
    rest (Nat.beq t 0)) (Nat.land g (nat_lit 3))

@[expose] noncomputable def kidsL (i : Nat) (L G : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun _ => List.nil)
    (fun y _ ih G => List.rec (motive := fun _ => List Nat) List.nil
      (fun g G' _ => kids i y g (ih G')) G) L G

@[expose] noncomputable def eqL (l m : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun m => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) m)
    (fun a _ ih m => List.rec (motive := fun _ => Bool) false
      (fun b m' _ => bAnd(Nat.beq a b, ih m')) m) l m

@[expose] noncomputable def kidsOK (i : Nat) (L L' G : List Nat) : Bool :=
  bAnd(List.rec (motive := fun _ => Bool) true
      (fun y _ ih => bAnd(andB (nwOK y) (Nat.blt y (gw i)), ih)) L,
    bAnd(Nat.beq (lenL L) (lenL G), eqL (kidsL i L G) L'))

@[expose] noncomputable def repsOK (TB : Nat) (B : List Nat) (i : Nat) (L G : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
    (fun y _ ih G => List.rec (motive := fun _ => Bool) true
      (fun g G' _ => bAnd(repOK TB B i y g, ih G')) G) L G

@[expose] noncomputable def finOK (TB : Nat) (B : List Nat) (RP y f : Nat) : Bool :=
  (fun t a d =>
    bIf(Nat.beq t (nat_lit 0), Nat.beq y (nat_lit 0),
      bIf(Nat.beq t (nat_lit 1),
        bAnd(nwOK a, bAnd(notB (Nat.beq a (nat_lit 0)), eqO TB B [y, y, y] [a])),
        bAnd(Nat.beq t (nat_lit 2), bAnd(Nat.blt a (nat_lit 824), bAnd(nwOK d,
          eqO TB B [d, y] [f32 RP a, d]))))))
    (Nat.land f (nat_lit 3)) (fld(f, nat_lit 2, nat_lit 4294967295)) (Nat.shiftRight f (nat_lit 34))

@[expose] noncomputable def finsOK (TB : Nat) (B : List Nat) (RP : Nat) (L F : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
    (fun y _ ih F => List.rec (motive := fun _ => Bool) true
      (fun f F' _ => bAnd(finOK TB B RP y f, ih F')) F) L F

@[expose] noncomputable def dropL {α : Type} (n : Nat) (l : List α) : List α :=
  Nat.rec (motive := fun _ => List α → List α) (fun l => l)
    (fun _ ih l => ih (List.rec (motive := fun _ => List α) List.nil (fun _ t _ => t) l)) n l

@[expose] noncomputable def takeL {α : Type} (n : Nat) (l : List α) : List α :=
  List.rec (motive := fun _ => Nat → List α) (fun _ => List.nil)
    (fun a _ ih n => Nat.rec (motive := fun _ => List α) List.nil (fun m _ => List.cons a (ih m)) n) l n

@[expose] noncomputable def letOK (ws : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun w _ ih => bAnd(List.rec (motive := fun _ => Bool) true
      (fun l _ ih2 => bAnd(Nat.blt l (nat_lit 26), ih2)) w, ih)) ws

@[expose] noncomputable def transOK (NW XW : Nat → Nat → Nat) (RP l : Nat) (w t : List Nat) : Bool :=
  andB (nwOK (f32 RP l))
    (List.rec (motive := fun _ => Bool) true
      (fun b _ ih => bAnd(Nat.beq (apP (letN NW) w (apP (letN NW) t b))
        (apP (letN NW) t (apP (letN XW) (nwL (f32 RP l)) b)), ih)) cb)

end CFSG.KC.Fi24Pc

end
