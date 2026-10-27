module

public import Certificates.Data.Kernel.BfsPin

public section

namespace CFSG.KC.HexaK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim
open CFSG.KLie.CT (anyN sumN andB orB notB)

@[expose] noncomputable def pgC (n w t x : Nat) : Nat := nIf(Nat.blt x n, pg w (mask w) t x, nat_lit 0)

@[expose] noncomputable def mul (n w a b : Nat) : Nat := pcomp n w (mask w) a b

@[expose] noncomputable def inv (n w a : Nat) : Nat := pinvS n w (mask w) a

@[expose] noncomputable def conj (n w g y : Nat) : Nat :=
  strictN g fun g => mul n w g (mul n w y (inv n w g))

@[expose] noncomputable def conjInv (n w g y : Nat) : Nat :=
  strictN g fun g => mul n w (inv n w g) (mul n w y g)

@[expose] noncomputable def commu (n w g h : Nat) : Nat :=
  strictN g fun g => strictN h fun h => mul n w (mul n w g h) (mul n w (inv n w g) (inv n w h))

@[expose] noncomputable def comm (n w a b : Nat) : Bool :=
  strictB a fun a => strictB b fun b => Nat.beq (mul n w a b) (mul n w b a)

@[expose] noncomputable def inL (N : Nat) (T : Nat → Nat) (x : Nat) : Bool :=
  strictB x fun x => anyN N fun j => Nat.beq x (T j)

@[expose] noncomputable def invCent (n w N : Nat) (T : Nat → Nat) (t : Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun r ih acc => (fun a =>
      Bool.rec (motive := fun _ => List Nat) (ih acc) (ih (a :: acc))
        (andB (comm n w a t) (andB (Nat.beq (mul n w a a) (pidn n w))
          (notB (Nat.beq a (pidn n w)))))) (T r)) N []

@[expose] noncomputable def noE8 (n w : Nat) (I : List Nat) : Bool :=
  I.all fun a => I.all fun b => I.all fun c =>
    orB (notB (andB (comm n w a b) (andB (comm n w a c) (comm n w b c))))
      (orB (Nat.beq b a) (orB (Nat.beq c a) (orB (Nat.beq c b) (Nat.beq c (mul n w a b)))))

@[expose] noncomputable def orbitAt (n w : Nat) (TT : Nat → Nat) (NM : Nat) (TM : Nat → Nat)
    (t0 : Nat) (W : List Nat) (i : Nat) : Bool :=
  strictB (TT i) fun t =>
    orB (orB (Nat.beq t (pidn n w))
      (andB (Nat.blt (W.getD i 0) NM) (Nat.beq (conj n w (TM (W.getD i 0)) t) t0)))
      (noE8 n w (invCent n w NM TM t))

@[expose] noncomputable def orbitK (n w NT : Nat) (TT : Nat → Nat) (NM : Nat) (TM : Nat → Nat)
    (t0 : Nat) (W : List Nat) : Bool :=
  (List.range NT).all (orbitAt n w TT NM TM t0 W)

@[expose] noncomputable def moveK (n w NM : Nat) (TM : Nat → Nat) (gc : Nat) (GC : Nat → Nat)
    (gr : Nat) (GR : Nat → Nat) (NR : Nat) (TR : Nat → Nat) : Bool :=
  allN NM fun j => strictB (TM j) fun m => anyN gc fun k => anyN gr fun r =>
    notB (inL NR TR (conjInv n w m (conj n w (GC k) (conj n w m (GR r)))))

@[expose] noncomputable def normalK (n w NT : Nat) (TT : Nat → Nat) (NC : Nat) (TC : Nat → Nat)
    (NN : Nat) (TN : Nat → Nat) (t0 : Nat) : Bool :=
  (invCent n w NC TC t0).all fun a => orB (inL NN TN a)
    (anyN NT fun t => strictB (TT t) fun x => andB (notB (Nat.beq x (pidn n w)))
      (andB (notB (Nat.beq x t0)) ((invCent n w NC TC t0).all fun b =>
        orB (notB (comm n w a b)) (comm n w b x))))

@[expose] noncomputable def blockK (n w k NC : Nat) (TC : Nat → Nat) (blk rep : Array Nat) : Bool :=
  andB ((List.range k).all fun i => andB (Nat.blt rep[i]! n) (Nat.beq blk[rep[i]!]! i))
    (allN NC fun j => strictB (TC j) fun t => (List.range n).all fun v =>
      orB (notB (Nat.blt blk[v]! k))
        (andB (Nat.blt blk[pgC n w t v]! k)
          (Nat.beq blk[pgC n w t v]! blk[pgC n w t rep[blk[v]!]!]!)))

@[expose] noncomputable def faithfulK (n w NC : Nat) (TC : Nat → Nat) (blk rep : Array Nat)
    (k : Nat) (blk' rep' : Array Nat) (k' : Nat) : Bool :=
  allN NC fun j => strictB (TC j) fun t =>
    orB (notB ((List.range k).all fun i => Nat.beq blk[pgC n w t rep[i]!]! i))
      (orB (notB ((List.range k').all fun i => Nat.beq blk'[pgC n w t rep'[i]!]! i))
        (Nat.beq t (pidn n w)))

@[expose] noncomputable def countK (n w NM : Nat) (TM : Nat → Nat) (t0 : Nat) : Nat :=
  sumN NM fun j => Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) (comm n w (TM j) t0)

@[expose] noncomputable def pow4 (n w a : Nat) : Nat :=
  mul n w a (mul n w a (mul n w a (mul n w a (pidn n w))))

@[expose] noncomputable def gensK (n w gT : Nat) (GT : Nat → Nat) (gM : Nat) (GM : Nat → Nat)
    (gC : Nat) (GC : Nat → Nat) (gN : Nat) (GN : Nat → Nat) (gR : Nat) (GR : Nat → Nat)
    (NT : Nat) (TT : Nat → Nat) (NM : Nat) (TM : Nat → Nat) (NN : Nat) (TN : Nat → Nat)
    (t0 : Nat) : Bool :=
  andB (allN gR fun k => inL NT TT (GR k))
  (andB (allN gM fun k => allN gT fun q => inL NT TT (conj n w (GM k) (GT q)))
  (andB (allN gC fun k => inL NM TM (GC k))
  (andB (allN gC fun k => comm n w (GC k) t0)
  (andB (allN gC fun k => Nat.beq (pow4 n w (GC k)) (pidn n w))
    (allN gC fun k => allN gN fun q => inL NN TN (conj n w (GC k) (GN q)))))))

@[expose] noncomputable def fuseK (n w NT : Nat) (TT : Nat → Nat) (NM : Nat) (TM : Nat → Nat)
    (NN : Nat) (TN : Nat → Nat) (t0 a x m : Nat) : Bool :=
  andB (Nat.blt a NN) (andB (Nat.blt x NT) (andB (Nat.blt m NM)
    (strictB (commu n w (TN a) (TT x)) fun c => andB (notB (Nat.beq c (pidn n w)))
      (andB (notB (Nat.beq c t0)) (Nat.beq (conj n w (TM m) c) t0)))))

end CFSG.KC.HexaK

end
