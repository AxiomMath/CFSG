module

public import Certificates.Data.Kernel.SporSch.TitsEnum5
public import Certificates.Data.Kernel.Spor.Prim

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.Mathieu

@[expose] noncomputable def pgR (p i : Nat) : Nat :=
  pg 11 (mask 11) (Nat.land (Nat.shiftRight p (Nat.mul (nat_lit 704) (Nat.div i (nat_lit 64))))
    (mask (nat_lit 704))) (Nat.mod i (nat_lit 64))

@[expose] noncomputable def eq22R (n x g : Nat) : Bool :=
  allN n (fun i => Nat.beq (pgR x (pgR g i)) (pgR g (pgR x i)))

@[expose] noncomputable def okPw (S SI : Nat → Nat) (wd : List Int) : Bool :=
  bAnd(lettersK (nat_lit 13) wd,
    strictB (wordK 1755 11 (mask 11) (pidn 1755 11) S SI wd) (fun x =>
    strictB (pinvS 1755 11 (mask 11) x) (fun xi =>
      bAnd(canonK 1755 11 (mask 11) (1755 * 11) x, bAnd(canonK 1755 11 (mask 11) (1755 * 11) xi,
        permOK 1755 11 (mask 11) (1755 * 11) x xi)))))

@[expose] noncomputable def allA {α : Type} (f : α → Bool) (A : List α) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ ih => bAnd(f a, ih)) A

@[expose] noncomputable def zipA {α : Type} (f : α → Nat → Bool) (A : List α) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun L => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) L)
    (fun a _ ih L => List.rec (motive := fun _ => Bool) false (fun l L' _ => bAnd(f a l, ih L')) L)
    A

@[expose] noncomputable def conjB (S SI : Nat → Nat) (Z T : Nat) (bw : Bool × List Int) (y : Nat) :
    Bool :=
  Prod.rec (motive := fun _ => Bool) (fun b wd =>
    strictB (wordK 1755 11 (mask 11) (pidn 1755 11) S SI wd) (fun x =>
      Nat.beq (pcomp 1755 11 (mask 11) (pcomp 1755 11 (mask 11) x
        (Bool.rec (motive := fun _ => Nat) T Z b)) (pinvS 1755 11 (mask 11) x)) y)) bw

@[expose] noncomputable def exclB (S SI : Nat → Nat) (T : Nat) (pw : Nat × List Int) (y : Nat) :
    Bool :=
  Prod.rec (motive := fun _ => Bool) (fun _ wd =>
    strictB (wordK 1755 11 (mask 11) (pidn 1755 11) S SI wd) (fun x =>
      Nat.beq (pcomp 1755 11 (mask 11) (pcomp 1755 11 (mask 11) (pinvS 1755 11 (mask 11) x) T) x)
        y)) pw

@[expose] noncomputable def memN (p : Nat) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun y _ ih => bIf(Nat.beq p y, true, ih)) L

@[expose] noncomputable def filterEqK (f : Nat → Bool) (L : List Nat) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun Q => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) Q)
    (fun x _ ih Q => bIf(f x,
      List.rec (motive := fun _ => Bool) false (fun q Q' _ => bAnd(Nat.beq x q, ih Q')) Q,
      ih Q)) L

@[expose] noncomputable def gptR (t0 t1 t2 t3 t4 i : Nat) : Nat :=
  pgR t0 (pgR t1 (pgR t2 (pgR t3 (pgR t4 i))))

@[expose] noncomputable def sqGR (G t0 t1 t2 t3 t4 : Nat) : Bool :=
  allN 1755 (fun i => strictB (gptR t0 t1 t2 t3 t4 (pgR G i)) (fun j =>
    Nat.beq (gptR t0 t1 t2 t3 t4 (pgR G j)) i))

@[expose] noncomputable def sqR (t0 t1 t2 t3 t4 : Nat) : Bool :=
  allN 1755 (fun i => Nat.beq (gptR t0 t1 t2 t3 t4 (gptR t0 t1 t2 t3 t4 i)) i)

@[expose] noncomputable def eqR (Z t0 t1 t2 t3 t4 : Nat) : Bool :=
  allN 1755 (fun i => Nat.beq (gptR t0 t1 t2 t3 t4 i) (pgR Z i))

@[expose] noncomputable def memR (L : List Nat) (t0 t1 t2 t3 t4 : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun y _ ih => bIf(eqR y t0 t1 t2 t3 t4, true, ih)) L

@[expose] noncomputable def conjR (T y t0 t1 t2 t3 t4 : Nat) : Bool :=
  allN 1755 (fun i => Nat.beq (gptR t0 t1 t2 t3 t4 (pgR T i)) (pgR y (gptR t0 t1 t2 t3 t4 i)))

@[expose] noncomputable def commR (G t0 t1 t2 t3 t4 : Nat) : Bool :=
  allN 1755 (fun i => Nat.beq (gptR t0 t1 t2 t3 t4 (pgR G i)) (pgR G (gptR t0 t1 t2 t3 t4 i)))

@[expose] noncomputable def zipProdP (LR TR : Nat → Nat) (c l : Nat) : Bool :=
  bAnd(canonK 1755 11 (mask 11) (1755 * 11) l,
  strictB (rcnt (LR 1)) (fun c1 => strictB (rcnt (LR 2)) (fun c2 =>
  strictB (rcnt (LR 3)) (fun c3 => strictB (rcnt (LR 4)) (fun c4 =>
  strictB (Nat.div c c4) (fun k3 => strictB (Nat.div k3 c3) (fun k2 =>
  strictB (Nat.div k2 c2) (fun k1 => strictB (Nat.div k1 c1) (fun a =>
  eqR l (trAt 1755 (1755 * 11) LR TR 0 a) (trAt 1755 (1755 * 11) LR TR 1 (Nat.mod k1 c1))
    (trAt 1755 (1755 * 11) LR TR 2 (Nat.mod k2 c2)) (trAt 1755 (1755 * 11) LR TR 3 (Nat.mod k3 c3))
    (trAt 1755 (1755 * 11) LR TR 4 (Nat.mod c c4)))))))))))

@[expose] noncomputable def pgS (p i : Nat) : Nat :=
  pg 11 (mask 11) (Nat.land (Nat.shiftRight p
    (Nat.add (nat_lit 64) (Nat.mul (nat_lit 704) (Nat.div i (nat_lit 64))))) (mask (nat_lit 704)))
    (Nat.mod i (nat_lit 64))

@[expose] noncomputable def canonS (l : Nat) : Bool :=
  bAnd(Nat.beq (Nat.shiftRight l (Nat.add (nat_lit 64) (1755 * 11))) (nat_lit 0),
    allN 1755 (fun i => Nat.blt (pgS l i) 1755))

@[expose] noncomputable def zipProdS (LR TR : Nat → Nat) (c l : Nat) : Bool :=
  bAnd(canonS l,
  strictB (rcnt (LR 1)) (fun c1 => strictB (rcnt (LR 2)) (fun c2 =>
  strictB (rcnt (LR 3)) (fun c3 => strictB (rcnt (LR 4)) (fun c4 =>
  strictB (Nat.div c c4) (fun k3 => strictB (Nat.div k3 c3) (fun k2 =>
  strictB (Nat.div k2 c2) (fun k1 => strictB (Nat.div k1 c1) (fun a =>
  strictB (trAt 1755 (1755 * 11) LR TR 0 a) (fun t0 =>
  strictB (trAt 1755 (1755 * 11) LR TR 1 (Nat.mod k1 c1)) (fun t1 =>
  strictB (trAt 1755 (1755 * 11) LR TR 2 (Nat.mod k2 c2)) (fun t2 =>
  strictB (trAt 1755 (1755 * 11) LR TR 3 (Nat.mod k3 c3)) (fun t3 =>
  strictB (trAt 1755 (1755 * 11) LR TR 4 (Nat.mod c c4)) (fun t4 =>
  allN 1755 (fun i => Nat.beq (gptR t0 t1 t2 t3 t4 i) (pgS l i))))))))))))))))

@[expose] noncomputable def eq22S (x g : Nat) : Bool :=
  allN 1755 (fun i => Nat.beq (pgS x (pgS g i)) (pgS g (pgS x i)))

@[expose] noncomputable def wPt (S SI : Nat → Nat) (wd : List Int) (i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun i => i)
    (fun z _ ih i => strictN (icode z) (fun c => strictN (ih i) (fun j =>
      pgR (nIf(Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 0),
        S (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)),
        SI (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)))) j))) wd i

@[expose] noncomputable def conjW (S SI : Nat → Nat) (wd : List Int) (A y : Nat) : Bool :=
  bAnd(lettersK (nat_lit 13) wd,
    allN 1755 (fun i => Nat.beq (wPt S SI wd (pgR A i)) (pgR y (wPt S SI wd i))))

@[expose] noncomputable def exclW (S SI : Nat → Nat) (wd : List Int) (T y : Nat) : Bool :=
  bAnd(lettersK (nat_lit 13) wd,
    allN 1755 (fun i => Nat.beq (wPt S SI wd (pgR y i)) (pgR T (wPt S SI wd i))))

@[expose] noncomputable def siftPf (LR TRI : Nat → Nat) (BP : Nat) (f : Nat) :
    Nat → (Nat → Nat) → Bool :=
  Nat.rec (motive := fun _ => Nat → (Nat → Nat) → Bool)
    (fun _ g => allN 1755 (fun i => Nat.beq (g i) i))
    (fun _ ih l g => strictB (LR l) (fun R =>
      strictB (rpos 11 (mask 11) (1755 * 11) R (g (pg 11 (mask 11) BP l))) (fun k =>
      bIf(Nat.blt k (rcnt R),
        strictB (TRI (Nat.add (roff 1755 (1755 * 11) R) k)) (fun t =>
          ih (Nat.succ l) (fun i => pgR t (g i))),
        false))))
    f

@[expose] noncomputable def siftP (LR TRI : Nat → Nat) (BP nb G : Nat) : Bool :=
  siftPf LR TRI BP nb 0 (fun i => pgR G i)

@[expose] noncomputable def siftPS (LR TRI : Nat → Nat) (BP nb G : Nat) : Bool :=
  siftPf LR TRI BP nb 0 (fun i => pgS G i)

end CFSG.KS.SporSch

end
