module

public import Certificates.Data.Kernel.O8.SARoots

public section

namespace CFSG.KC.O8

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def rec0At (SC PT LT L i : Nat) : Nat :=
  strictN (saAtK SC i) fun a => strictN (lookL L (matMulK a a)) fun k =>
    nIf(Nat.beq k (nat_lit 0), nat_lit 0, nIf(Nat.beq (parK PT LT i) (nat_lit 0),
      Nat.add (Nat.add (nat_lit 1048576) (Nat.mul (nat_lit 128) i))
        (Nat.mul (nat_lit 2) (Nat.sub k (nat_lit 1))), nat_lit 0))

@[expose] noncomputable def roots0K (SC PT LT L : Nat) : Nat :=
  foldN (nat_lit 8192) (fun i acc => strictN (rec0At SC PT LT L i) fun r =>
    nIf(Nat.beq r (nat_lit 0), acc, Nat.lor (Nat.shiftLeft acc (nat_lit 21)) r)) (nat_lit 0)

@[expose] noncomputable def rootN (e : Nat × Nat × Nat × Nat × List (Nat × Nat))
    (f : Nat → Nat → Nat → Nat → List (Nat × Nat) → Nat) : Nat :=
  Prod.rec (motive := fun _ => Nat) (fun i t => Prod.rec (motive := fun _ => Nat) (fun k t =>
    Prod.rec (motive := fun _ => Nat) (fun r t =>
      Prod.rec (motive := fun _ => Nat) (fun c pl => f i k r c pl) t) t) t) e

@[expose] noncomputable def rootB (e : Nat × Nat × Nat × Nat × List (Nat × Nat))
    (f : Nat → Nat → Nat → Nat → List (Nat × Nat) → Bool) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun i t => Prod.rec (motive := fun _ => Bool) (fun k t =>
    Prod.rec (motive := fun _ => Bool) (fun r t =>
      Prod.rec (motive := fun _ => Bool) (fun c pl => f i k r c pl) t) t) t) e

@[expose] noncomputable def recsJ (R : List (Nat × Nat × Nat × Nat × List (Nat × Nat))) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun e _ ih => strictN ih fun a =>
    Nat.lor (rootN e fun i k _ _ _ => Nat.add (Nat.add (nat_lit 1048576)
      (Nat.mul (nat_lit 128) i)) (Nat.mul (nat_lit 2) k)) (Nat.shiftLeft a (nat_lit 21))) R

@[expose] noncomputable def repsJ (R : List (Nat × Nat × Nat × Nat × List (Nat × Nat))) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun e _ ih => strictN ih fun a =>
    rootN e fun i _ r _ _ => nIf(Nat.beq r i, Nat.lor a (Nat.shiftLeft (nat_lit 1) i), a)) R

@[expose] noncomputable def allRoots (R : List (Nat × Nat × Nat × Nat × List (Nat × Nat)))
    (f : Nat × Nat × Nat × Nat × List (Nat × Nat) → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun e _ ih => bAnd(f e, ih)) R

@[expose] noncomputable def bitK (m p : Nat) : Bool :=
  Nat.blt (nat_lit 0) (Nat.land m (Nat.shiftLeft (nat_lit 1) p))

@[expose] noncomputable def rootOK (SC PT LT YP CR : Nat)
    (e : Nat × Nat × Nat × Nat × List (Nat × Nat)) : Bool :=
  rootB e fun i k r c _ => bAnd(bitK CR r, bAnd(Nat.blt c (nat_lit 8192),
    bAnd(Nat.beq (parK PT LT c) (nat_lit 0),
      strictB (saAtK SC c) fun C => strictB (saAtK YP k) fun y =>
        bAnd(Nat.beq (matMulK C (saAtK SC i)) (matMulK (saAtK SC r) C),
          Nat.beq (matMulK C y) (matMulK y C)))))

@[expose] noncomputable def antiQK (R ry V : Nat) : Bool :=
  Nat.beq (matMulK V R) (matMulK ry V)

@[expose] noncomputable def cntK (SC : Nat) (R0 : List (Nat × Nat × Nat × Nat × List (Nat × Nat)))
    (k R ry : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun e _ ih => strictN ih fun a =>
    rootN e fun j k' _ _ _ => nIf(bAnd(Nat.beq k' k, antiQK R ry (saAtK SC j)), Nat.succ a, a)) R0

@[expose] noncomputable def codesK (SC : Nat) (l : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun a _ ih => saAtK SC a :: ih) l

@[expose] noncomputable def listAtK (SC : Nat) (Ls : List (List Nat)) (j : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun l _ ih j => Bool.rec (motive := fun _ => List Nat) (ih (Nat.sub j (nat_lit 1)))
      (codesK SC l) (Nat.beq j (nat_lit 0))) Ls j

@[expose] noncomputable def subK (xs L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => bAnd(memK x L, ih)) xs

@[expose] noncomputable def witK (R V : Nat) (Q : List Nat) (C D e a b : Nat) : Bool :=
  strictB (matMulK (matMulK C R) D) fun cr => strictB (matMulK (matMulK C V) D) fun cv =>
  strictB (nIf(Nat.beq a (nat_lit 0), R, V)) fun x => strictB (nIf(Nat.beq b (nat_lit 0), cr, cv)) fun z =>
    bAnd(bIf(memK (nIf(Nat.beq e (nat_lit 0), cr, cv)) Q, false, true),
      bIf(Nat.beq (matMulK x z) (matMulK z x), false, true))

@[expose] noncomputable def tagOK (SC : Nat) (Ls : List (List Nat)) (C0 D0 C1 D1 C2 D2 : Nat)
    (k y R V tag : Nat) : Bool :=
  strictB (matMulK R y) fun ry => strictB (matMulK V y) fun vy => strictB (matMulK R V) fun rv =>
  strictB (matMulK rv y) fun rvy =>
  bIf(Nat.beq (Nat.mod tag (nat_lit 4)) (nat_lit 0),
    bAnd(Nat.beq k (nat_lit 10), bAnd(Nat.blt tag (nat_lit 16),
      subK [idK, y, R, ry, V, vy, rv, rvy] (listAtK SC Ls (Nat.div tag (nat_lit 4))))),
    strictB (Nat.sub tag (nat_lit 1)) fun t => strictB (Nat.land t (nat_lit 7)) fun w =>
      bAnd(Nat.blt tag (nat_lit 64),
      bAnd(bIf(Nat.beq k (nat_lit 10), Nat.blt w (nat_lit 2),
        bAnd(Nat.beq k (nat_lit 37), Nat.beq w (nat_lit 2))),
      witK R V [idK, y, R, ry, V, vy, rv, rvy]
        (nIf(Nat.beq w (nat_lit 0), C0, nIf(Nat.beq w (nat_lit 1), C1, C2)))
        (nIf(Nat.beq w (nat_lit 0), D0, nIf(Nat.beq w (nat_lit 1), D1, D2)))
        (fld(t, nat_lit 3, nat_lit 1)) (fld(t, nat_lit 4, nat_lit 1)) (fld(t, nat_lit 5, nat_lit 1)))))

@[expose] noncomputable def plK (SC PT LT : Nat) (Ls : List (List Nat)) (C0 D0 C1 D1 C2 D2 : Nat)
    (k y R ry : Nat) (pl : List (Nat × Nat)) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 1)
    (fun p _ ih lo => Prod.rec (motive := fun _ => Nat) (fun v tag =>
      strictN (saAtK SC v) fun V =>
      nIf(bAnd(Nat.blt lo v, bAnd(Nat.blt v (nat_lit 8192), bAnd(Nat.beq (parK PT LT v) (nat_lit 0),
        bAnd(Nat.beq (matMulK V V) y, bAnd(antiQK R ry V,
          tagOK SC Ls C0 D0 C1 D1 C2 D2 k y R V tag))))),
        strictN (ih v) fun n => nIf(Nat.beq n (nat_lit 0), nat_lit 0, Nat.succ n), nat_lit 0)) p) pl

@[expose] noncomputable def pairsOK (SC PT LT YP : Nat) (Ls : List (List Nat))
    (C0 D0 C1 D1 C2 D2 : Nat) (R0 : List (Nat × Nat × Nat × Nat × List (Nat × Nat)))
    (lo hi : Nat) (e : Nat × Nat × Nat × Nat × List (Nat × Nat)) : Bool :=
  rootB e fun i k r _ pl => bIf(bAnd(Nat.beq r i, bAnd(Nat.ble lo i, Nat.blt i hi)),
    strictB (saAtK SC i) fun R => strictB (saAtK YP k) fun y => strictB (matMulK R y) fun ry =>
      Nat.beq (plK SC PT LT Ls C0 D0 C1 D1 C2 D2 k y R ry pl (nat_lit 0))
        (Nat.succ (cntK SC R0 k R ry)), true)

@[expose] noncomputable def dsw1 (m d A : Nat) : Nat :=
  strictN (Nat.land (Nat.xor (Nat.shiftRight m d) m) A) fun t =>
    Nat.xor m (Nat.xor t (Nat.shiftLeft t d))

@[expose] noncomputable def dswK (sw : List (Nat × Nat)) (m : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun m => m)
    (fun p _ ih m => strictN (Prod.rec (motive := fun _ => Nat) (fun d A => dsw1 m d A) p) ih) sw m

@[expose] noncomputable def swAtK (SW : List (List (Nat × Nat))) (l m : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => m)
    (fun sw _ ih l => nIf(Nat.beq l (nat_lit 0), dswK sw m, ih (Nat.sub l (nat_lit 1)))) SW l

@[expose] noncomputable def swTie (G : Nat → Nat) (SW : List (List (Nat × Nat))) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun r => Nat.beq r (nat_lit 8))
    (fun sw _ ih r => strictB (G r) fun X => bAnd(allN (nat_lit 240) (fun a =>
      strictB (pg (nat_lit 9) (nat_lit 511) X a) fun x => bAnd(Nat.blt x (nat_lit 240),
        Nat.beq (dswK sw (Nat.shiftLeft (nat_lit 1) a)) (Nat.shiftLeft (nat_lit 1) x))),
      ih (Nat.succ r))) SW (nat_lit 0)

@[expose] noncomputable def rowW (r : Nat) : Nat := Nat.land r (nat_lit 1208925819614629174706175)

@[expose] noncomputable def rowP (r : Nat) : Nat := fld(r, nat_lit 80, nat_lit 65535)

@[expose] noncomputable def rowS (r : Nat) : Nat := fld(r, nat_lit 96, nat_lit 65535)

@[expose] noncomputable def rowN (r : Nat) : Nat := fld(r, nat_lit 112, nat_lit 65535)

@[expose] noncomputable def memRowK (RT MT : Nat → Nat) (SW : List (List (Nat × Nat)))
    (M0 X0 k : Nat) : Bool :=
  strictB (RT k) fun r => strictB (MT k) fun m => strictB (rowW r) fun w =>
  bAnd(bIf(Nat.beq k (nat_lit 0), bAnd(Nat.beq w (nat_lit 0), Nat.beq m M0),
      strictB (rowP r) fun p => strictB (Nat.land w (nat_lit 15)) fun l =>
        bAnd(Nat.blt p (nat_lit 6300), bAnd(Nat.blt (nat_lit 0) l, bAnd(Nat.blt l (nat_lit 9),
        bAnd(Nat.beq (rowW (RT p)) (Nat.shiftRight w (nat_lit 4)),
          Nat.beq m (swAtK SW (Nat.sub l (nat_lit 1)) (MT p))))))),
    strictB (rowN r) fun n => strictB (Nat.shiftRight n (nat_lit 9)) fun t =>
    strictB (Nat.land n (nat_lit 511)) fun q =>
      bIf(Nat.beq t (nat_lit 0), bAnd(Nat.blt q (nat_lit 240), bAnd(bitK m q,
          strictB (pg (nat_lit 9) (nat_lit 511) X0 q) fun x => bAnd(Nat.blt x (nat_lit 240),
            bIf(bitK m x, false, true)))),
        bIf(Nat.beq t (nat_lit 3), bIf(Nat.beq k (nat_lit 0), true, bIf(Nat.beq k (nat_lit 1), true,
            bIf(Nat.beq k (nat_lit 3), true, Nat.beq k (nat_lit 4)))),
          Nat.blt t (nat_lit 3))))

@[expose] noncomputable def letK (GT l p : Nat) : Nat :=
  nIf(Nat.beq l (nat_lit 0), p,
    pg (nat_lit 9) (nat_lit 511) GT (Nat.add (Nat.mul (nat_lit 360) (Nat.sub l (nat_lit 1))) p))

@[expose] noncomputable def walkUp (GT w q : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) q (fun i ih => strictN ih fun p =>
    letK GT (fld(w, Nat.mul (nat_lit 4) i, nat_lit 15)) p) (nat_lit 20)

@[expose] noncomputable def walkDn (GT w q : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) q (fun i ih => strictN ih fun p =>
    letK GT (fld(w, Nat.mul (nat_lit 4) (Nat.sub (nat_lit 19) i), nat_lit 15)) p) (nat_lit 20)

@[expose] noncomputable def gtK (G : Nat → Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun l ih => strictN ih fun a => Nat.lor a (Nat.shiftLeft (G l) (Nat.mul (nat_lit 3240) l))) n

@[expose] noncomputable def walkOK (RT : Nat → Nat) (GT F U V k : Nat) : Bool :=
  strictB (RT k) fun r => strictB (rowW r) fun w => strictB (rowN r) fun n =>
  strictB (Nat.shiftRight n (nat_lit 9)) fun t => strictB (Nat.land n (nat_lit 511)) fun q =>
    bIf(bAnd(Nat.blt (nat_lit 0) t, Nat.blt t (nat_lit 3)),
      bAnd(Nat.blt q (nat_lit 360), bAnd(bitK F q,
        strictB (walkUp GT w q) fun p =>
        strictB (pg (nat_lit 9) (nat_lit 511) (nIf(Nat.beq t (nat_lit 1), U, V)) p) fun p' =>
          bIf(bitK F (walkDn GT w p'), false, true))), true)

@[expose] noncomputable def sortAt (RT MT : Nat → Nat) (i : Nat) : Bool :=
  strictB (rowS (RT i)) fun s => bAnd(Nat.blt s (nat_lit 6300),
    bIf(Nat.blt i (nat_lit 6299), Nat.blt (MT s) (MT (rowS (RT (Nat.succ i)))), true))

@[expose] noncomputable def packW (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun a _ ih => Nat.add a (Nat.shiftLeft ih (nat_lit 4))) w

@[expose] noncomputable def wTieK (RT : Nat → Nat) (E : List (List Nat × (Nat × Nat))) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun k => Nat.beq k (nat_lit 6300))
    (fun row _ ih k => bAnd(Prod.rec (motive := fun _ => Bool)
        (fun w _ => Nat.beq (packW w) (rowW (RT k))) row, strictB (Nat.succ k) ih)) E (nat_lit 0)

@[expose] noncomputable def fixMK (U V n : Nat) : Nat :=
  foldN n (fun p acc => nIf(bAnd(Nat.beq (pg (nat_lit 9) (nat_lit 511) U p) p,
      Nat.beq (pg (nat_lit 9) (nat_lit 511) V p) p),
    Nat.lor acc (Nat.shiftLeft (nat_lit 1) p), acc)) (nat_lit 0)

end CFSG.KC.O8

end
