module

public import Certificates.Data.Kernel.BalanceSC.Check
public import Certificates.Data.Kernel.Misc.ArrEnum

public section

namespace CFSG.KC.Sol5Q

open CFSG.KC.Enum (pg pcomp strictN strictB)
open CFSG.KS (pinvS)
open CFSG.KC.BalanceSC (notB tab64 memL anyL zipAll)
open CFSG.KC.Misc.ArrEnum (permB)

@[expose] noncomputable def pc (n p q : Nat) : Nat := pcomp n (nat_lit 4) (nat_lit 15) p q

@[expose] noncomputable def pinv (n p : Nat) : Nat := pinvS n (nat_lit 4) (nat_lit 15) p

@[expose] noncomputable def pw (n e p k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) e (fun _ ih => strictN ih (fun q => pc n p q)) k

@[expose] noncomputable def fixC (n p : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i ih => Nat.add ih (nIf(Nat.beq (pg (nat_lit 4) (nat_lit 15) p i) i, nat_lit 1, nat_lit 0))) n

@[expose] noncomputable def badK (n e r : Nat) : Bool :=
  bAnd(Nat.beq (pc n r r) e, bAnd(notB (Nat.beq r e), Nat.ble (nat_lit 4) (fixC n r)))

@[expose] noncomputable def cjK (n HB x j : Nat) : Nat :=
  strictN (tab64 HB j) fun h => pc n h (pc n x (pinv n h))

@[expose] noncomputable def commK (n a b : Nat) : Nat :=
  pc n (pc n a b) (pc n (pinv n a) (pinv n b))

@[expose] noncomputable def elK (n S HB x c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) S (fun j _ => cjK n HB x j) c

@[expose] noncomputable def prodK (n e S HB x : Nat) (cs : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun c _ ih acc => strictN (pc n acc (elK n S HB x c)) ih) cs e

@[expose] noncomputable def allL (L : List Nat) (f : Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun d _ ih => bAnd(f d, ih)) L

@[expose] noncomputable def atL (L : List Nat) (i : Nat) (f : Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => false)
    (fun d _ ih i => Nat.rec (motive := fun _ => Bool) (f d) (fun j _ => ih j) i) L i

@[expose] noncomputable def emptyL {α : Type} (L : List α) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) L

@[expose] noncomputable def ctOK (n S card : Nat) (CT : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Nat → Bool) (fun _ c => Nat.beq c card)
    (fun x _ ih lo c => bAnd(Nat.ble lo x, bAnd(permB n (nat_lit 4) x,
      bAnd(Nat.beq (pc n S x) (pc n x S), strictB (Nat.succ c) (ih (Nat.succ x))))))
    CT (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def hOK (n e HB NH : Nat) (HG : List Nat) (HPL : List (Nat × Nat)) : Bool :=
  bAnd(Nat.beq (tab64 HB (nat_lit 0)) e,
    List.rec (motive := fun _ => Nat → Bool) (fun k => Nat.beq k NH)
      (fun pl _ ih k => bAnd(Nat.blt pl.1 k, bAnd(atL HG pl.2 fun g =>
          Nat.beq (tab64 HB k) (pc n (tab64 HB pl.1) g), strictB (Nat.succ k) ih)))
      HPL (nat_lit 1))

@[expose] noncomputable def gensK (n e S : Nat) (HG : List Nat) : Bool :=
  allL HG fun g => bAnd(permB n (nat_lit 4) g, bAnd(Nat.beq (pc n S g) (pc n g S),
    bIf(Nat.beq (pw n e g (nat_lit 3)) e, true,
      bAnd(Nat.beq (pc n g g) e, bAnd(Nat.beq (fixC n g) (Nat.sub n (nat_lit 8)),
        Nat.beq (fixC n (pc n g S)) (Nat.sub n (nat_lit 8)))))))

@[expose] noncomputable def evK (n e w m : Nat) : Bool :=
  bAnd(notB (Nat.beq (pw n e w m) e), Nat.beq (pw n e w (Nat.add m m)) e)

@[expose] noncomputable def fcbK (n e HB NH : Nat) (BN CT : List Nat) (RB : List (List Nat)) : Bool :=
  zipAll (fun b r => List.rec (motive := fun _ => Bool) false (fun t rest _ =>
      bIf(Nat.beq t (nat_lit 0), atL rest (nat_lit 0) (evK n e b),
      bIf(Nat.beq t (nat_lit 1), memL b BN,
        atL rest (nat_lit 0) fun h => atL rest (nat_lit 1) fun m =>
          bAnd(Nat.blt h NH, strictB (pc n b (cjK n HB b h)) fun w => evK n e w m)))) r) CT RB

@[expose] noncomputable def rowK (n e : Nat) (big : Bool) (BN Sl : List Nat) (CT : List Nat) :
    List Nat → List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → List Nat → Bool)
    (fun row GL => bAnd(emptyL row, emptyL GL))
    (fun g _ ih row GL => List.rec (motive := fun _ => Bool) false
      (fun c row' _ => Nat.rec (motive := fun _ => Bool)
        (bIf(big, List.rec (motive := fun _ => Bool) false
            (fun a GL' _ => bAnd(Nat.beq a g, ih row' GL')) GL,
          bAnd(Nat.beq (pw n e g (nat_lit 8)) e, ih row' GL)))
        (fun i _ => bAnd(atL Sl i fun t =>
            notB (anyL BN fun b => Nat.beq (pc n g t) (pc n (pc n b t) g)), ih row' GL)) c) row) CT

@[expose] noncomputable def goodK (n e HB NH : Nat) (big : Bool) (BN CT : List Nat) (x : Nat)
    (js : List Nat) (g : List Nat × List Nat × List Nat × List Nat) : Bool :=
  bAnd(zipAll (fun j s => bAnd(Nat.blt j NH, Nat.beq (cjK n HB x j) s)) js g.1,
    bAnd(rowK n e big BN g.1 CT g.2.1 g.2.2.1,
      bIf(big, bAnd(allL g.2.2.1 fun a => allL g.2.2.1 fun b => memL (commK n a b) g.2.2.2,
          allL g.2.2.2 fun u => allL g.2.2.2 fun v => Nat.beq (pc n u v) (pc n v u)), true)))

@[expose] noncomputable def fcrK (n e S HB NH : Nat) (big : Bool) (BN CT : List Nat)
    (RR : List (List Nat)) (GD : List (List Nat × List Nat × List Nat × List Nat)) : Bool :=
  List.rec
    (motive := fun _ => List (List Nat) → List (List Nat × List Nat × List Nat × List Nat) → Bool)
    (fun RR GD => bAnd(emptyL RR, emptyL GD))
    (fun x _ ih RR GD => List.rec (motive := fun _ => Bool) false (fun r RR' _ =>
      List.rec (motive := fun _ => Bool) false (fun t rest _ =>
        bIf(Nat.beq t (nat_lit 0), bAnd(notB (Nat.beq (pw n e x (nat_lit 8)) e), ih RR' GD),
        bIf(Nat.beq t (nat_lit 1), bAnd(bIf(Nat.beq x e, true, Nat.beq x S), ih RR' GD),
        bIf(Nat.beq t (nat_lit 2), bAnd(allL rest (fun c => Nat.ble c NH),
            bAnd(badK n e (prodK n e S HB x rest), ih RR' GD)),
          List.rec (motive := fun _ => Bool) false
            (fun g GD' _ => bAnd(goodK n e HB NH big BN CT x rest g, ih RR' GD')) GD)))) r) RR)
    CT RR GD

@[expose] noncomputable def fco2K (n e HB NH : Nat) (big : Bool) (FO : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun i r1 _ => List.rec (motive := fun _ => Bool) false
    (fun j r2 _ => bAnd(Nat.blt i NH, bAnd(Nat.blt j NH,
      strictB (tab64 HB i) fun a => strictB (tab64 HB j) fun b =>
      List.rec (motive := fun _ => Bool)
        (bAnd(notB big, bAnd(Nat.beq (pw n e a (nat_lit 3)) e,
          bAnd(Nat.beq (pw n e b (nat_lit 3)) e, badK n e (pc n a b)))))
        (fun k r3 _ => List.rec (motive := fun _ => Bool) false (fun l r4 _ =>
          bAnd(big, bAnd(emptyL r4, bAnd(Nat.blt k NH, bAnd(Nat.blt l NH,
            badK n e (commK n (commK n a b) (commK n (tab64 HB k) (tab64 HB l)))))))) r3) r2))) r1) FO

end CFSG.KC.Sol5Q

end
