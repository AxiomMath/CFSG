module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.L34Syl

open CFSG.KC.Enum

@[expose] noncomputable def lane (lw lm T k : Nat) : Nat := fld(T, Nat.mul lw k, lm)

@[expose] noncomputable def bNot (b : Bool) : Bool := bIf(b, false, true)

@[expose] noncomputable def canonP (n w m nw x : Nat) : Bool :=
  bAnd(Nat.beq (Nat.shiftRight x nw) (nat_lit 0), allN n (fun i => Nat.blt (pg w m x i) n))

@[expose] noncomputable def invPt (n w m x y : Nat) : Bool :=
  allN n (fun i => Nat.beq (pg w m x (pg w m y i)) i)

@[expose] noncomputable def idPt (n w m x : Nat) : Bool :=
  allN n (fun i => Nat.beq (pg w m x i) i)

@[expose] noncomputable def lettersOK (n w m nw : Nat) (L : Nat → Nat) (ng : Nat) : Bool :=
  allN ng (fun j => strictB (L (Nat.mul (nat_lit 2) j)) (fun a =>
    strictB (L (Nat.succ (Nat.mul (nat_lit 2) j))) (fun b =>
      bAnd(canonP n w m nw a, bAnd(canonP n w m nw b, invPt n w m b a)))))

@[expose] noncomputable def ltL (nl : Nat) (ws : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun l _ ih => bAnd(Nat.blt l nl, ih)) ws

@[expose] noncomputable def wv (w m : Nat) (L : Nat → Nat) (ws : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun l _ ih x => ih (pg w m (L l) x)) ws x

@[expose] noncomputable def wvI (w m : Nat) (L : Nat → Nat) (ws : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun l _ ih x => pg w m (L (Nat.xor l (nat_lit 1))) (ih x)) ws x

@[expose] noncomputable def wordK (n w m nl : Nat) (L : Nat → Nat) (ws : List Nat) (tgt : Nat) :
    Bool :=
  bAnd(ltL nl ws, allN n (fun i => Nat.beq (wv w m L ws i) (pg w m tgt i)))

@[expose] noncomputable def commK (n w m nl : Nat) (L : Nat → Nat) (u v : List Nat) (tgt : Nat) :
    Bool :=
  bAnd(ltL nl u, bAnd(ltL nl v, allN n (fun i =>
    Nat.beq (wv w m L u (wv w m L v (wvI w m L u (wvI w m L v i)))) (pg w m tgt i))))

@[expose] noncomputable def grpE (n w m nw pm b bm : Nat) (L : Nat → Nat) (ng T D N k : Nat) :
    Bool :=
  strictB (lane nw pm T k) (fun x => strictB (lane (nat_lit 64) (nat_lit 18446744073709551615) D k)
    (fun d => strictB fld(d, Nat.add (Nat.add b (nat_lit 4)) (Nat.mul b ng), nat_lit 255) (fun dep =>
    bAnd(canonP n w m nw x,
    bAnd(bIf(Nat.beq k (nat_lit 0), true, Nat.blt (lane nw pm T (Nat.sub k (nat_lit 1))) x),
    bAnd(bIf(Nat.beq dep (nat_lit 0), idPt n w m x,
      strictB fld(d, nat_lit 0, bm) (fun par => strictB fld(d, b, nat_lit 15) (fun l =>
        bAnd(Nat.blt par N, bAnd(Nat.blt l (Nat.mul (nat_lit 2) ng),
        bAnd(Nat.beq (Nat.succ fld(lane (nat_lit 64) (nat_lit 18446744073709551615) D par,
            Nat.add (Nat.add b (nat_lit 4)) (Nat.mul b ng), nat_lit 255)) dep,
          eq2 n w m x (L l) (lane nw pm T par))))))),
    allN ng (fun j => strictB fld(d, Nat.add (Nat.add b (nat_lit 4)) (Nat.mul b j), bm) (fun c =>
      bAnd(Nat.blt c N, eq2 n w m (lane nw pm T c) (L (Nat.mul (nat_lit 2) j)) x)))))))))

@[expose] noncomputable def grpK (n w m nw pm b bm : Nat) (L : Nat → Nat) (ng T D N : Nat) : Bool :=
  bAnd(Nat.blt (nat_lit 0) N, allN N (fun k => grpE n w m nw pm b bm L ng T D N k))

@[expose] noncomputable def powsK (n w m nw pm p RT cnt : Nat) : Bool :=
  allN cnt (fun i => strictB (Nat.mul (Nat.sub p (nat_lit 1)) i) (fun base =>
    strictB (lane nw pm RT base) (fun r =>
    bAnd(canonP n w m nw r, bAnd(bNot (idPt n w m r),
    bAnd(allN (Nat.sub p (nat_lit 2)) (fun k =>
        strictB (lane nw pm RT (Nat.add base (Nat.succ k))) (fun a =>
        strictB (lane nw pm RT (Nat.add base k)) (fun c => eq2 n w m a c r))),
      strictB (lane nw pm RT (Nat.add base (Nat.sub p (nat_lit 2)))) (fun l => invPt n w m l r)))))))

@[expose] noncomputable def canonW (w m X y1 : Nat) : Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ ih y => strictB (pg w m X y) (fun y' => bAnd(Nat.blt y1 y', ih y')))

@[expose] noncomputable def recE (n w m nw pm p nc nt PT RT hi lo X ix : Nat) : Bool :=
  strictB (Nat.land ix (nat_lit 15)) (fun c =>
  strictB (Nat.land (Nat.shiftRight ix (nat_lit 4)) (nat_lit 4095)) (fun t =>
  strictB (Nat.shiftRight ix (nat_lit 16)) (fun a =>
  bAnd(Nat.blt lo X, bAnd(Nat.ble X hi, bAnd(Nat.blt c nc, bAnd(Nat.blt t nt,
  bAnd(Nat.beq (Nat.shiftRight X nw) (nat_lit 0),
  bAnd(strictB (lane nw pm PT c) (fun C => strictB (lane nw pm RT t) (fun RK =>
      eq22 n w m X C C RK)),
  bAnd(Nat.blt a n, bAnd(allN a (fun i => Nat.beq (pg w m X i) i),
    strictB (pg w m X a) (fun y1 =>
      bAnd(bNot (Nat.beq y1 a), canonW w m X y1 (Nat.sub p (nat_lit 2)) y1)))))))))))))

@[expose] noncomputable def recsK (n w m nw pm p nc nt PT RT hi : Nat) (L : List (Nat × Nat))
    (lo : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun e _ ih lo => Prod.rec (motive := fun _ => Bool)
      (fun X ix => bAnd(recE n w m nw pm p nc nt PT RT hi lo X ix, ih X)) e) L lo

@[expose] noncomputable def img (n w m g s : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i ih => Nat.lor ih (nIf(Nat.blt (nat_lit 0) (Nat.land s (Nat.shiftLeft (nat_lit 1) i)),
      Nat.shiftLeft (nat_lit 1) (pg w m g i), nat_lit 0))) n

@[expose] noncomputable def orbE (n w m om : Nat) (L : Nat → Nat) (ng H OM OD N k : Nat) : Bool :=
  strictB (lane n om OM k) (fun s => strictB (lane (nat_lit 64) (nat_lit 18446744073709551615) OD k)
    (fun d => strictB fld(d, nat_lit 42, nat_lit 63) (fun dep =>
    bAnd(bIf(Nat.beq k (nat_lit 0), true, Nat.blt (lane n om OM (Nat.sub k (nat_lit 1))) s),
    bAnd(bIf(Nat.beq dep (nat_lit 0), Nat.beq s H,
      strictB fld(d, nat_lit 0, nat_lit 63) (fun par => strictB fld(d, nat_lit 6, nat_lit 3) (fun g =>
        bAnd(Nat.blt par N, bAnd(Nat.blt g ng,
        bAnd(Nat.beq (Nat.succ fld(lane (nat_lit 64) (nat_lit 18446744073709551615) OD par,
            nat_lit 42, nat_lit 63)) dep,
          Nat.beq s (img n w m (L (Nat.mul (nat_lit 2) g)) (lane n om OM par)))))))),
    allN ng (fun j => strictB fld(d, Nat.add (nat_lit 8) (Nat.mul (nat_lit 6) j), nat_lit 63)
      (fun c => bAnd(Nat.blt c N,
        Nat.beq (lane n om OM c) (img n w m (L (Nat.mul (nat_lit 2) j)) s)))))))))

@[expose] noncomputable def orbK (n w m om : Nat) (L : Nat → Nat) (ng H OM OD N : Nat) : Bool :=
  allN N (fun k => orbE n w m om L ng H OM OD N k)

@[expose] noncomputable def cntK (N : Nat) (f : Nat → Bool) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun k ih => nIf(f k, Nat.succ ih, ih)) N

@[expose] noncomputable def subE (n w m om : Nat) (LM : Nat → Nat) (nlab R OM OD N k : Nat) : Bool :=
  strictB (lane n om OM k) (fun s => strictB (lane (nat_lit 64) (nat_lit 18446744073709551615) OD k)
    (fun d => strictB fld(d, nat_lit 26, nat_lit 3) (fun c => strictB fld(d, nat_lit 36, nat_lit 63)
    (fun dep => bAnd(Nat.blt c nlab,
      bIf(Nat.beq dep (nat_lit 0), Nat.beq fld(R, Nat.mul (nat_lit 6) c, nat_lit 63) k,
      strictB fld(d, nat_lit 28, nat_lit 63) (fun par => strictB fld(d, nat_lit 34, nat_lit 3) (fun g =>
        strictB (lane (nat_lit 64) (nat_lit 18446744073709551615) OD par) (fun dp =>
        bAnd(Nat.blt par N, bAnd(Nat.blt g (nat_lit 3),
        bAnd(Nat.beq fld(dp, nat_lit 26, nat_lit 3) c,
        bAnd(Nat.beq (Nat.succ fld(dp, nat_lit 36, nat_lit 63)) dep,
          Nat.beq s (img n w m (LM (Nat.mul (nat_lit 2) g)) (lane n om OM par)))))))))))))))

@[expose] noncomputable def subK (n w m om : Nat) (LM : Nat → Nat) (nlab R CN H OM OD N : Nat) :
    Bool :=
  bAnd(allN (nat_lit 3) (fun j => Nat.beq (img n w m (LM (Nat.mul (nat_lit 2) j)) H) H),
  bAnd(allN N (fun k => subE n w m om LM nlab R OM OD N k),
    allN nlab (fun c => Nat.beq (cntK N (fun k =>
      Nat.beq fld(lane (nat_lit 64) (nat_lit 18446744073709551615) OD k, nat_lit 26, nat_lit 3) c))
      fld(CN, Nat.mul (nat_lit 8) c, nat_lit 255))))

@[expose] noncomputable def restrK (n w m : Nat) (LM SX : Nat → Nat) (HP H : Nat) : Bool :=
  bAnd(allN (nat_lit 6) (fun a => bAnd(Nat.blt (pg w m HP a) n,
    allN (nat_lit 6) (fun b => bIf(Nat.beq a b, true, bNot (Nat.beq (pg w m HP a) (pg w m HP b)))))),
  bAnd(Nat.beq (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun k ih => Nat.lor ih (Nat.shiftLeft (nat_lit 1) (pg w m HP k))) (nat_lit 6)) H,
    allN (nat_lit 3) (fun j => allN (nat_lit 6) (fun k =>
      Nat.beq (pg w m (LM (Nat.mul (nat_lit 2) j)) (pg w m HP k))
        (pg w m HP (pg (nat_lit 3) (nat_lit 7) (SX (Nat.mul (nat_lit 2) j)) k))))))

@[expose] noncomputable def pm252 : Nat :=
  nat_lit 7237005577332262213973186563042994240829374041602535252466099000494570602495

@[expose] noncomputable def hOf (n om OM R : Nat) : Nat := lane n om OM fld(R, nat_lit 0, nat_lit 63)

@[expose] noncomputable def letX (lw lm LP r r' l : Nat) : Nat :=
  nIf(Nat.blt l (nat_lit 4), lane lw lm LP l, nIf(Nat.beq l (nat_lit 4), r, r'))

@[expose] noncomputable def rowsK (n w m nw pm p ntg LP RT TG : Nat) (rows : List (Nat × List Nat))
    (i : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun e _ ih i => Prod.rec (motive := fun _ => Bool) (fun tg ws =>
      bAnd(Nat.blt tg ntg,
      bAnd(strictB (Nat.mul (Nat.sub p (nat_lit 1)) i) (fun base =>
        strictB (lane nw pm RT base) (fun r =>
        strictB (lane nw pm RT (Nat.add base (Nat.sub p (nat_lit 2)))) (fun r' =>
          wordK n w m (nat_lit 6) (letX nw pm LP r r') ws (lane nw pm TG tg)))),
        ih (Nat.succ i)))) e) rows i

@[expose] noncomputable def wordsK (n w m nl : Nat) (L tg : Nat → Nat) (ws : List (List Nat))
    (i : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun u _ ih i => bAnd(strictB (tg i) (fun r => wordK n w m nl L u r), ih (Nat.succ i))) ws i

@[expose] noncomputable def commsK (n w m nl : Nat) (L tg : Nat → Nat)
    (prs : List (List Nat × List Nat)) (i : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun e _ ih i => Prod.rec (motive := fun _ => Bool) (fun u v =>
      bAnd(strictB (tg i) (fun r => commK n w m nl L u v r), ih (Nat.succ i))) e) prs i

end CFSG.KC.L34Syl

end
