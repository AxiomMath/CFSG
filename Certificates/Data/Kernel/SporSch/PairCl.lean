module

public import Certificates.Data.Kernel.SporSch.PairK
public import Certificates.Data.Kernel.SporSch.SetReplay

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def trK (n nw : Nat) (LR TR : Nat → Nat) (i k : Nat) : Nat :=
  TR (Nat.add (roff n nw (LR i)) k)

@[expose] noncomputable def triK (n nw : Nat) (LR TRI : Nat → Nat) (i k : Nat) : Nat :=
  TRI (Nat.add (roff n nw (LR i)) k)

@[expose] noncomputable def nfPt (n w : Nat) (LR TR : Nat → Nat) (nb NF x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun i ih x => strictN (pg w (mask w) (trK n (Nat.mul n w) LR TR i fld(NF, Nat.mul (nat_lit 16) i,
      nat_lit 65535)) x) ih)
    nb x

@[expose] noncomputable def keyL (n : Nat) (f : Nat → Nat) (bs : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun b _ ih => strictN ih (fun r => Nat.add (f b) (Nat.mul n r))) bs

@[expose] noncomputable def nfKey (n w : Nat) (LR TR : Nat → Nat) (nb : Nat) (bs : List Nat)
    (NF : Nat) : Nat :=
  keyL n (nfPt n w LR TR nb NF) bs

@[expose] noncomputable def wordKey (n w : Nat) (bs Ws : List Nat) : Nat := keyL n (evRK w Ws) bs

@[expose] noncomputable def conjKey (n w : Nat) (LR TR : Nat → Nat) (nb : Nat) (bs : List Nat)
    (G GI NF : Nat) : Nat :=
  keyL n (fun b => pg w (mask w) G (nfPt n w LR TR nb NF (pg w (mask w) GI b))) bs

@[expose] noncomputable def keyAt (n K t : Nat) : Nat :=
  Nat.mod (Nat.rec (motive := fun _ => Nat) K (fun _ k => strictN k (fun k' => Nat.div k' n)) t) n

@[expose] noncomputable def siftNF (n w : Nat) (LR TRI : Nat → Nat) (nb K : Nat) : Nat :=
  (Nat.rec (motive := fun _ => (Nat → Nat) → Nat × Nat)
    (fun _ => (nat_lit 0, nat_lit 0))
    (fun i ih cur => (fun k =>
      Prod.rec (motive := fun _ => Nat × Nat) (fun acc _ =>
        (Nat.lor acc (Nat.shiftLeft k (Nat.mul (nat_lit 16) (Nat.sub (Nat.sub nb (nat_lit 1)) i))), k))
        (ih (fun t => pg w (mask w) (triK n (Nat.mul n w) LR TRI (Nat.sub (Nat.sub nb (nat_lit 1)) i) k)
          (cur t))))
      (rpos w (mask w) (Nat.mul n w) (LR (Nat.sub (Nat.sub nb (nat_lit 1)) i))
        (cur (Nat.sub (Nat.sub nb (nat_lit 1)) i))))
    nb (keyAt n K)).1

@[expose] noncomputable def nfX (nb x : Nat) : Nat := Nat.land x (mask (Nat.mul (nat_lit 16) nb))

@[expose] noncomputable def nfKeyX (n w : Nat) (LR TR : Nat → Nat) (nb : Nat) (bs : List Nat)
    (XT : Nat → Nat) (rx i : Nat) : Nat :=
  nfKey n w LR TR nb bs (nfX nb (rowGet XT rx i))

@[expose] noncomputable def parNF (nb x : Nat) : Nat :=
  fld(x, Nat.mul (nat_lit 16) nb, nat_lit 1048575)

@[expose] noncomputable def labNF (nb x : Nat) : Nat :=
  fld(x, Nat.add (Nat.mul (nat_lit 16) nb) (nat_lit 20), nat_lit 255)

@[expose] noncomputable def stepNF (n w : Nat) (LR TR TRI : Nat → Nat) (nb : Nat) (bs : List Nat)
    (G GI X W : Nat → Nat) (c h l cur : Nat) : Nat :=
  nIf(Nat.blt h cur,
    strictN (conjKey n w LR TR nb bs (G l) (GI l) (nfX nb (X h))) (fun kz =>
    strictN fld(W h, Nat.mul (nat_lit 20) l, nat_lit 1048575) (fun j =>
    strictN (X j) (fun xj =>
    strictN (nfKey n w LR TR nb bs (nfX nb xj)) (fun kj =>
      nIf(bAnd(Nat.blt j cur, Nat.beq kj kz), cur,
      nIf(bAnd(Nat.beq j cur, bAnd(Nat.beq kj kz,
          bAnd(Nat.beq (nfX nb xj) (siftNF n w LR TRI nb kz),
          bAnd(Nat.beq (parNF nb xj) h, Nat.beq (labNF nb xj) l)))),
        Nat.succ cur, failC)))))),
    nIf(Nat.beq cur c, cur, failC))

@[expose] noncomputable def runNF (n w : Nat) (LR TR TRI : Nat → Nat) (nb : Nat) (bs : List Nat)
    (G GI X W : Nat → Nat) (kg c : Nat) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ cur => cur)
    (fun _ ih h cur => strictN (foldUp kg (fun l cur => stepNF n w LR TR TRI nb bs G GI X W c h l cur)
      cur) (fun c' => strictN (Nat.succ h) (fun h' => ih h' c')))

@[expose] noncomputable def startNF (n w : Nat) (LR TRI : Nat → Nat) (nb : Nat) (bs RP : List Nat)
    (x : Nat) : Bool :=
  bAnd(Nat.beq (nfX nb x) (siftNF n w LR TRI nb (wordKey n w bs RP)),
    bAnd(Nat.beq (parNF nb x) (nat_lit 0), Nat.beq (labNF nb x) (nat_lit 0)))

@[expose] noncomputable def nfOKAt (_n _w : Nat) (LR : Nat → Nat) (nb : Nat) (X : Nat → Nat) (c i : Nat) :
    Bool :=
  bIf(Nat.blt i c, strictB (X i) (fun x => allN nb (fun t =>
    Nat.blt fld(x, Nat.mul (nat_lit 16) t, nat_lit 65535) (rcnt (LR t)))), true)

@[expose] noncomputable def sumN (m : Nat) (f : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun i acc => strictN acc (fun a => Nat.add (f i) a)) m

@[expose] noncomputable def cnt3 (n w : Nat) (LR TR : Nat → Nat) (bs : List Nat) (m : Nat)
    (XP : List Nat) (conds : List (List Bool × Nat)) (k0 : Nat) : Nat :=
  strictN (Nat.mul n w) (fun nw => strictN (trK n nw LR TR 0 k0) (fun t0 =>
  foldUp (rcnt (LR 1)) (fun k1 s => strictN (trK n nw LR TR 1 k1) (fun t1 =>
    foldUp (rcnt (LR 2)) (fun k2 s => strictN (trK n nw LR TR 2 k2) (fun t2 =>
      nIf(ordB0 w bs [t2, t1, t0] m,
        nIf(condsK w bs XP [t2, t1, t0] conds, Nat.add s (nat_lit 1048577), Nat.succ s), s))) s)) (nat_lit 0)))
where
  condsK (w : Nat) (bs XP YP : List Nat) (conds : List (List Bool × Nat)) : Bool :=
    List.rec (motive := fun _ => Bool) true
      (fun c _ ih => Prod.rec (motive := fun _ => Bool)
        (fun pat o => bAnd(ordB0 w bs (patWK XP YP pat) o, ih)) c) conds
  appK (a b : List Nat) : List Nat :=
    List.rec (motive := fun _ => List Nat) b (fun x _ ih => x :: ih) a
  patWK (XP YP : List Nat) (pat : List Bool) : List Nat :=
    List.rec (motive := fun _ => List Nat) []
      (fun b _ ih => appK ih (Bool.rec (motive := fun _ => List Nat) XP YP b)) pat

end CFSG.KS.SporSch

end
