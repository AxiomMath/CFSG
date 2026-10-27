module

public import Certificates.Data.Kernel.Spor.MEnum

public section

namespace CFSG.KS.MEnum

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu CFSG.KS.M11

@[expose] noncomputable def allFrom (p : Nat → Bool) : Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ ih lo => bAnd(p lo, ih (Nat.succ lo)))

@[expose] noncomputable def itr (f : Nat → Nat) (k i : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) i (fun _ x => f x) k

@[expose] noncomputable def powId (n : Nat) (f : Nat → Nat) (k : Nat) : Bool :=
  allFrom (fun i => Nat.beq (itr f k i) i) n (nat_lit 0)

@[expose] noncomputable def ord6Z (n : Nat) (f : Nat → Nat) : Bool :=
  bAnd(Bool.not (powId n f (nat_lit 1)), bAnd(Bool.not (powId n f (nat_lit 2)),
    bAnd(Bool.not (powId n f (nat_lit 3)), powId n f (nat_lit 6))))

@[expose] noncomputable def ordPZ (n r : Nat) (f : Nat → Nat) : Bool :=
  bAnd(powId n f r, Bool.not (powId n f (nat_lit 1)))

@[expose] noncomputable def partZ (n w m ky r R Ri : Nat) (g : Nat → Nat) : Bool :=
  bAnd(ordPZ n r (fun i => pg w m R (g i)),
    ord6Z n (fun i => pg w m R (g (pg w m Ri (itr g (Nat.sub ky (nat_lit 1)) i)))))

@[expose] noncomputable def partsZ (n w m ky r : Nat) (g : Nat → Nat) (Rs : List (Nat × Nat)) :
    Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun p _ ih e => Prod.rec (motive := fun _ => Nat) (fun R Ri =>
      Nat.add (nIf(partZ n w m ky r R Ri g, Nat.shiftLeft (nat_lit 1) e, nat_lit 0))
        (ih (Nat.add e (nat_lit 40)))) p) Rs

@[expose] noncomputable def memsZ (n w m : Nat) (g : Nat → Nat) (Rs : List (Nat × Nat)) :
    Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun p _ ih e => Prod.rec (motive := fun _ => Nat) (fun R _ =>
      Nat.add (nIf(allFrom (fun i => Nat.beq (g i) (pg w m R i)) n (nat_lit 0),
          Nat.shiftLeft (nat_lit 1) e, nat_lit 0))
        (ih (Nat.add e (nat_lit 40)))) p) Rs

@[expose] noncomputable def cntZ (n w m ky r : Nat) (Rs : List (Nat × Nat)) (g : Nat → Nat)
    (s : Nat) : Nat :=
  nIf(powId n g (nat_lit 2),
    nIf(powId n g (nat_lit 1), s, Nat.add (Nat.succ s) (memsZ n w m g Rs (nat_lit 60))),
    nIf(powId n g ky,
      Nat.add s (Nat.add (nat_lit 1048576) (partsZ n w m ky r g Rs (nat_lit 40))),
      s))

@[expose] noncomputable def lastZ (n w m nw pm ky r : Nat) (Rs : List (Nat × Nat)) (L3 L4 h s : Nat) :
    Nat :=
  foldUp (lcnt L3) (fun k3 s => strictN (ltr nw pm L3 k3) (fun t3 =>
    foldUp (lcnt L4) (fun k4 s => strictN (ltr nw pm L4 k4) (fun t4 =>
      cntZ n w m ky r Rs (fun x => pg w m h (pg w m t3 (pg w m t4 x))) s)) s)) s

@[expose] noncomputable def sliceZ (n w m nw pm ky r : Nat) (Rs : List (Nat × Nat))
    (L0 L1 L2 L3 L4 sub i : Nat) : Nat :=
  strictN (Nat.div (lcnt L1) sub) (fun q =>
  strictN (ltr nw pm L0 (Nat.div i sub)) (fun g0 =>
  foldUp q (fun j s => strictN (pcomp n w m g0
      (ltr nw pm L1 (Nat.add (Nat.mul q (Nat.mod i sub)) j))) (fun h1 =>
    foldUp (lcnt L2) (fun k2 s => strictN (pcomp n w m h1 (ltr nw pm L2 k2)) (fun h =>
      lastZ n w m nw pm ky r Rs L3 L4 h s)) s)) (nat_lit 0)))

@[expose] noncomputable def five (Ls : List Nat) (k : Nat → Nat → Nat → Nat → Nat → Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun L0 r1 _ =>
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun L1 r2 _ =>
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun L2 r3 _ =>
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun L3 r4 _ =>
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun L4 _ _ => k L0 L1 L2 L3 L4) r4) r3) r2) r1) Ls

@[expose] noncomputable def mCntZ (n w : Nat) (bs : List Nat) (NW : Nat) (tA tB : List Nat)
    (W : List (List Int)) (sub i ky r : Nat) (Rs : List (Nat × Nat)) : Nat :=
  strictN (mask w) (fun m => strictN (Nat.mul n w) (fun nw => strictN (mask nw) (fun pm =>
  strictN (pidn n w) (fun idn => strictN (Nat.add NW NW) (fun NL =>
  strictN (mLT n w tA tB W) (fun LT =>
  levN n w m nw pm idn LT NL bs (mask NL) (fun Ls _ =>
    five Ls (fun L0 L1 L2 L3 L4 => sliceZ n w m nw pm ky r Rs L0 L1 L2 L3 L4 sub i))))))))

@[expose] noncomputable def clsOneR (n w : Nat) (tA tB : List Nat) (mx cap : Nat) (d : ClassDatum) :
    Bool :=
  strictB (mask w) (fun m => strictB (Nat.mul n w) (fun nw => strictB (mask nw) (fun pm =>
  strictB (packL w tA) (fun A => strictB (pinvS n w m A) (fun Ai =>
  strictB (packL w tB) (fun B => strictB (pinvS n w m B) (fun Bi =>
  Prod.rec (motive := fun _ => Bool) (fun _ d => Prod.rec (motive := fun _ => Bool) (fun _ d =>
  Prod.rec (motive := fun _ => Bool) (fun R d => Prod.rec (motive := fun _ => Bool) (fun Bl d =>
  Prod.rec (motive := fun _ => Bool) (fun P d => Prod.rec (motive := fun _ => Bool) (fun Lb S =>
    bAnd(allLtN (Nat.shiftLeft (nat_lit 1) nw) Bl, bAnd(allLtN (Nat.shiftLeft (nat_lit 1) nw) S,
      clsOK n w m nw pm A Ai B Bi mx cap R (packL nw Bl) P Lb (packL nw S) (lenN S)))) d) d) d)
    d) d) d)))))))

@[expose] def cntSum (CS : List Nat) (f : Nat) : Nat :=
  (CS.map fun v => (v >>> (20 * f)) % 2 ^ 20).sum

@[expose] def clsTotR (CL : List ClassDatum) (CS : List Nat) : Nat :=
  ((List.range CL.length).map fun j => (CL.getD j (0, 0, 0, [], [], [], [])).2.2.2.2.2.2.length *
    cntSum CS (2 + 2 * j)).sum

end CFSG.KS.MEnum

end
