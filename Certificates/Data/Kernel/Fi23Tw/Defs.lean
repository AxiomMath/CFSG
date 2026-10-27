module

public import Certificates.Data.Kernel.Fi23Y322.Defs

public section

namespace CFSG.KC.Fi23Tw

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23R CFSG.KC.Fi23Five CFSG.KC.Fi23Y322

@[expose] noncomputable def bitB (A k : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight A k) (nat_lit 1)) (nat_lit 1)

@[expose] noncomputable def nthL (L : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun a _ ih i => nIf(Nat.beq i (nat_lit 0), a, ih (Nat.pred i))) L

@[expose] noncomputable def dropL (L : List Nat) : Nat → List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun a L' ih i => Nat.rec (motive := fun _ => List Nat) (a :: L') (fun i' _ => ih i') i) L

@[expose] noncomputable def rowK (G : Nat → Nat) (A a i : Nat) (T : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun b _ ih j => bAnd(bIf(cmK G a b,
        bAnd(bitB A (Nat.add (Nat.mul (nat_lit 135) i) j),
          bitB A (Nat.add (Nat.mul (nat_lit 135) j) i)),
        bAnd(Bool.not (bitB A (Nat.add (Nat.mul (nat_lit 135) i) j)),
          Bool.not (bitB A (Nat.add (Nat.mul (nat_lit 135) j) i)))),
      ih (Nat.succ j))) T

@[expose] noncomputable def matK (G : Nat → Nat) (A : Nat) (F : List Nat) (lo c : Nat) : Bool :=
  allN c fun l => strictB (Nat.add lo l) fun i =>
    rowK G A (nthL F i) i (dropL F (Nat.succ i)) (Nat.succ i)

@[expose] noncomputable def rowA (A i : Nat) : Nat :=
  Nat.land (Nat.shiftRight A (Nat.mul (nat_lit 135) i))
    (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 135)) (nat_lit 1))

@[expose] noncomputable def twB (A m : Nat) : Bool :=
  strictB (Nat.div m (nat_lit 135)) fun i => strictB (Nat.mod m (nat_lit 135)) fun j =>
    bAnd(Bool.not (Nat.beq i j), bAnd(Bool.not (bitB A m),
      Nat.beq (Nat.land (Nat.xor (rowA A i) (rowA A j))
        (Nat.xor (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 135)) (nat_lit 1))
          (Nat.lor (Nat.shiftLeft (nat_lit 1) i) (Nat.shiftLeft (nat_lit 1) j)))) (nat_lit 0)))

@[expose] noncomputable def twLoop (A : Nat) (n : Nat) : Nat → List Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → List Nat → Bool)
    (fun _ P => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) P)
    (fun _ ih m P => strictB m fun m => List.rec (motive := fun _ => Bool)
      (bAnd(Bool.not (twB A m), ih (Nat.succ m) P))
      (fun e P' _ => bIf(Nat.beq (Nat.land e (nat_lit 32767)) m, bAnd(twB A m, ih (Nat.succ m) P'),
        bAnd(Bool.not (twB A m), ih (Nat.succ m) P))) P) n

@[expose] noncomputable def peK (G : Nat → Nat) (F : List Nat) (e : Nat) : Bool :=
  strictB (Nat.land e (nat_lit 32767)) fun m =>
    strictB (Nat.land (Nat.shiftRight e (nat_lit 15)) (nat_lit 255)) fun k =>
      strictB (nthL F (Nat.div m (nat_lit 135))) fun a =>
        strictB (nthL F (Nat.mod m (nat_lit 135))) fun b =>
          strictB (nthL F k) fun c =>
            bAnd(Nat.blt k (nat_lit 135), bAnd(Nat.beq (tA G a b) c,
              bAnd(Bool.not (Nat.beq c a), bAnd(Bool.not (Nat.beq c b),
                Nat.beq (Nat.shiftRight e (nat_lit 23)) (tA G a (tA G b (nat_lit 0)))))))

@[expose] noncomputable def rotB (p q : Nat) : Bool :=
  strictB (Nat.land p (nat_lit 32767)) fun m =>
    strictB (Nat.div m (nat_lit 135)) fun i => strictB (Nat.mod m (nat_lit 135)) fun j =>
      strictB (Nat.land (Nat.shiftRight p (nat_lit 15)) (nat_lit 255)) fun k =>
        strictB (Nat.land q (nat_lit 32767)) fun mq =>
          bIf(Nat.beq mq m, true, bIf(Nat.beq mq (Nat.add (Nat.mul (nat_lit 135) j) k), true,
            Nat.beq mq (Nat.add (Nat.mul (nat_lit 135) k) i)))

@[expose] noncomputable def keyK (P : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun p _ ih => bAnd(
    List.rec (motive := fun _ => Bool) true (fun q _ ih' => bAnd(
      bIf(Nat.beq (Nat.shiftRight p (nat_lit 23)) (Nat.shiftRight q (nat_lit 23)), rotB p q, true),
      ih')) P, ih)) P

@[expose] noncomputable def trK (G : Nat → Nat) (T : List Nat) : Bool :=
  strictB (nthL T (nat_lit 0)) fun a => strictB (nthL T (nat_lit 1)) fun b =>
    strictB (nthL T (nat_lit 2)) fun c =>
      bAnd(Nat.beq (tA G a b) c, bAnd(Nat.beq (tA G b c) a, bAnd(Nat.beq (tA G c a) b,
        idK G [a, b, a, b, a, b])))

@[expose] noncomputable def pairIn (T : List Nat) (a b : Nat) : Bool :=
  strictB (nthL T (nat_lit 0)) fun x => strictB (nthL T (nat_lit 1)) fun y =>
    strictB (nthL T (nat_lit 2)) fun z =>
      bIf(bAnd(Nat.beq a x, Nat.beq b y), true, bIf(bAnd(Nat.beq a y, Nat.beq b z), true,
        bIf(bAnd(Nat.beq a z, Nat.beq b x), true, bIf(bAnd(Nat.beq a y, Nat.beq b x), true,
          bIf(bAnd(Nat.beq a z, Nat.beq b y), true, bAnd(Nat.beq a x, Nat.beq b z))))))

@[expose] noncomputable def inTr (F : List Nat) (TR : List (List Nat)) (e : Nat) : Bool :=
  strictB (Nat.land e (nat_lit 32767)) fun m =>
    strictB (nthL F (Nat.div m (nat_lit 135))) fun a =>
      strictB (nthL F (Nat.mod m (nat_lit 135))) fun b =>
        List.rec (motive := fun _ => Bool) false (fun T _ ih => bIf(pairIn T a b, true, ih)) TR

@[expose] noncomputable def cmTr (G : Nat → Nat) (T T' : List Nat) : Bool :=
  strictB (nthL T (nat_lit 0)) fun a => strictB (nthL T (nat_lit 1)) fun b =>
    strictB (nthL T (nat_lit 2)) fun c =>
      strictB (nthL T' (nat_lit 0)) fun a' => strictB (nthL T' (nat_lit 1)) fun b' =>
        strictB (tA G a' (tA G b' a)) fun u => strictB (tA G a' (tA G b' b)) fun v =>
          bIf(bAnd(Nat.beq u a, Nat.beq v b), true, bIf(bAnd(Nat.beq u b, Nat.beq v c), true,
            bAnd(Nat.beq u c, Nat.beq v a)))

@[expose] noncomputable def cmAll (G : Nat → Nat) (TR : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun T R ih => bAnd(
    List.rec (motive := fun _ => Bool) true (fun T' _ ih' => bAnd(cmTr G T T', ih')) R, ih)) TR

@[expose] noncomputable def tgK (G : Nat → Nat) (w : List Nat) (F : List Nat) (g : List Nat) :
    Bool :=
  strictB (nthL g (nat_lit 0)) fun c => strictB (nthL g (nat_lit 3)) fun P =>
    bAnd(Nat.blt c (nat_lit 31671), bAnd(Nat.beq (wv G w c) (nthL g (nat_lit 1)),
      bAnd(Nat.beq (wv G w (nthL g (nat_lit 1))) (nthL g (nat_lit 2)),
        List.rec (motive := fun _ => Bool) true
          (fun a _ ih => bAnd(bIf(cmK G a c, bitB P a, Bool.not (bitB P a)), ih)) F)))

@[expose] noncomputable def fixAll (G : Nat → Nat) (w : List Nat) (ws : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun a _ ih => bAnd(Nat.blt a (nat_lit 31671), bAnd(Nat.beq (wv G w a) a, ih))) ws

@[expose] noncomputable def cmV (G : Nat → Nat) (r : Nat) (ws : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun a _ ih => strictN ih fun v =>
      nIf(cmK G a r, Nat.succ (Nat.mul (nat_lit 2) v), Nat.mul (nat_lit 2) v)) ws

@[expose] noncomputable def sepB (P : Nat) (ws : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => false)
    (fun a _ ih V => bIf(bIf(bitB V (nat_lit 0), Bool.not (bitB P a), bitB P a), true,
      ih (Nat.shiftRight V (nat_lit 1)))) ws

@[expose] noncomputable def tg1 (g : List Nat) (r : Nat) (ws : List Nat) (V : Nat) : Bool :=
  bIf(Nat.beq r (nthL g (nat_lit 0)), true, bIf(Nat.beq r (nthL g (nat_lit 1)), true,
    bIf(Nat.beq r (nthL g (nat_lit 2)), true, sepB (nthL g (nat_lit 3)) ws V)))

@[expose] noncomputable def repK (G : Nat → Nat) (w : List Nat) (TG : List (List Nat))
    (e : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun r ws _ =>
    bAnd(Nat.blt r (nat_lit 31671), bAnd(fixAll G w ws, strictB (cmV G r ws) fun V =>
      List.rec (motive := fun _ => Bool) true (fun g _ ih => bAnd(tg1 g r ws V, ih)) TG))) e

@[expose] noncomputable def repAll (G : Nat → Nat) (w : List Nat) (TG : List (List Nat))
    (R : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun e _ ih => bAnd(repK G w TG e, ih)) R

@[expose] noncomputable def orbBits (G : Nat → Nat) (w : List Nat) (r : Nat) : Nat :=
  strictN (wv G w r) fun y => strictN (wv G w y) fun z =>
    Nat.lor (Nat.lor (Nat.shiftLeft (nat_lit 1) r) (Nat.shiftLeft (nat_lit 1) y))
      (Nat.shiftLeft (nat_lit 1) z)

@[expose] noncomputable def allL (f : Nat → Bool) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ ih => bAnd(f a, ih)) L

@[expose] noncomputable def allLL (f : List Nat → Bool) (L : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ ih => bAnd(f a, ih)) L

@[expose] noncomputable def covU (G : Nat → Nat) (w : List Nat) (R : List (List Nat)) :
    Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun e _ ih acc => strictN (Nat.lor acc (orbBits G w (nthL e (nat_lit 0)))) ih) R

end CFSG.KC.Fi23Tw

end
