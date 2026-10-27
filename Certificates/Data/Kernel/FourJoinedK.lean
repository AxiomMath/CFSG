module

public import Certificates.Data.Kernel.Q16BK

public section

namespace CFSG.KC.FourJ

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.Q16BK

@[expose] noncomputable def wordR (n w : Nat) (lf L : Nat → Nat) (len : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => pidn n w)
    (fun _ ih o => pcomp n w (mask w) (lf (L o)) (ih (Nat.succ o))) len

@[expose] noncomputable def wordT (n w : Nat) (lf O L : Nat → Nat) (t : Nat) : Nat :=
  wordR n w lf L (Nat.sub (O (Nat.succ t)) (O t)) (O t)

@[expose] noncomputable def let4 (a b c d l : Nat) : Nat :=
  nIf(Nat.beq l (nat_lit 0), a, nIf(Nat.beq l (nat_lit 1), b, nIf(Nat.beq l (nat_lit 2), c, d)))

@[expose] noncomputable def letX (n w nX : Nat) (Z ZI : Nat → Nat) (l : Nat) : Nat :=
  nIf(Nat.blt l nX, Z l, nIf(Nat.blt l (Nat.add nX nX), ZI (Nat.sub l nX), pidn n w))

@[expose] noncomputable def bitK (f i : Nat) : Bool := Nat.blt (nat_lit 0) (Nat.land f (Nat.shiftLeft 1 i))

@[expose] noncomputable def cmK (n w : Nat) (ps : List Nat) (x y : Nat) : Bool :=
  Nat.beq (keyWK n w ps [x, y]) (keyWK n w ps [y, x])

@[expose] noncomputable def fjGensK (n w A B AI BI ng : Nat) (G SO SL : Nat → Nat) : Bool :=
  bAnd(canonK n w (mask w) (Nat.mul n w) A, bAnd(canonK n w (mask w) (Nat.mul n w) B,
  bAnd(canonK n w (mask w) (Nat.mul n w) AI, bAnd(canonK n w (mask w) (Nat.mul n w) BI,
  bAnd(invEqK n w (mask w) (Nat.mul n w) A AI, bAnd(invEqK n w (mask w) (Nat.mul n w) B BI,
    allN ng fun k => Nat.beq (wordT n w (let4 A B AI BI) SO SL k) (G k)))))))

@[expose] noncomputable def fjKleinK (n w : Nat) (ps : List Nat) (N : Nat) (T : Nat → Nat) (m : Nat)
    (PX PY PXY : Nat → Nat) : Bool :=
  strictB (keyWK n w ps []) fun e => allN m fun i =>
    strictB (T (PX i)) fun x => strictB (T (PY i)) fun y =>
    bAnd(Nat.blt (PX i) N, bAnd(Nat.blt (PY i) N, bAnd(Nat.blt (PXY i) N,
    bAnd(Nat.blt (nat_lit 0) (PX i), bAnd(Nat.blt (nat_lit 0) (PY i),
    bAnd(bIf(Nat.beq (PX i) (PY i), false, true),
    bAnd(Nat.beq (keyWK n w ps [x, x]) e, bAnd(Nat.beq (keyWK n w ps [y, y]) e,
    bAnd(cmK n w ps x y, Nat.beq (keyWK n w ps [x, y]) (keyWK n w ps [T (PXY i)]))))))))))

@[expose] noncomputable def fjTreeK (n w : Nat) (ps : List Nat) (T : Nat → Nat) (m nBig : Nat)
    (PX PY PAR : Nat → Nat) : Bool :=
  bAnd(Nat.blt (nat_lit 0) nBig, bAnd(Nat.ble nBig m, allN nBig fun i =>
    bIf(Nat.beq i (nat_lit 0), true, strictB (PAR i) fun p =>
      strictB (T (PX i)) fun x => strictB (T (PY i)) fun y =>
      strictB (T (PX p)) fun x' => strictB (T (PY p)) fun y' =>
      bAnd(Nat.blt p i, bAnd(cmK n w ps x x', bAnd(cmK n w ps x y',
        bAnd(cmK n w ps y x', cmK n w ps y y')))))))

@[expose] noncomputable def fjIsoK (n w A B AI BI : Nat) (T : Nat → Nat) (m nBig : Nat)
    (PX PY IJ IO IL : Nat → Nat) : Bool :=
  allN (Nat.sub m nBig) fun t => strictB (Nat.add nBig t) fun i => strictB (IJ t) fun j =>
    strictB (wordT n w (let4 A B AI BI) IO IL t) fun g =>
    bAnd(Nat.blt j nBig,
      bAnd(Nat.beq (pcomp n w (mask w) g (T (PX j))) (pcomp n w (mask w) (T (PX i)) g),
        Nat.beq (pcomp n w (mask w) g (T (PY j))) (pcomp n w (mask w) (T (PY i)) g)))

@[expose] noncomputable def sel3 (n w x y c : Nat) : Nat :=
  nIf(Nat.beq c (nat_lit 0), x, nIf(Nat.beq c (nat_lit 1), y, pcomp n w (mask w) x y))

@[expose] noncomputable def fjNormK (n w A B AI BI : Nat) (T : Nat → Nat) (nBig nX : Nat)
    (PX PY NJ NCX NCY Z ZI NO NL : Nat → Nat) : Bool :=
  allN nX fun k => strictB (Z k) fun z => strictB (NJ k) fun j =>
    strictB (T (PX j)) fun x => strictB (T (PY j)) fun y =>
    bAnd(Nat.blt j nBig, bAnd(Nat.beq (wordT n w (let4 A B AI BI) NO NL k) z,
    bAnd(canonK n w (mask w) (Nat.mul n w) (ZI k), bAnd(invEqK n w (mask w) (Nat.mul n w) z (ZI k),
    bAnd(Nat.beq (pcomp n w (mask w) z x) (pcomp n w (mask w) (sel3 n w x y (NCX k)) z),
      Nat.beq (pcomp n w (mask w) z y) (pcomp n w (mask w) (sel3 n w x y (NCY k)) z))))))

@[expose] noncomputable def fjGenK (n w A B nX : Nat) (Z ZI UO UL : Nat → Nat) : Bool :=
  bAnd(Nat.beq (wordT n w (letX n w nX Z ZI) UO UL (nat_lit 0)) A,
    Nat.beq (wordT n w (letX n w nX Z ZI) UO UL (nat_lit 1)) B)

@[expose] noncomputable def fjCompK (n w : Nat) (ps : List Nat) (N : Nat) (T : Nat → Nat) (m : Nat)
    (PX PY PXY : Nat → Nat) (INV : Nat) (FM : Nat → Nat) : Bool :=
  strictB (keyWK n w ps []) fun e =>
  bAnd(allN N (fun u => bIf(bitK INV u, true,
      bIf(Nat.beq (keyWK n w ps [T u, T u]) e, Nat.beq u (nat_lit 0), true))),
  bAnd(allN N (fun u => strictB (FM u) fun f => bAnd(Nat.blt f (Nat.shiftLeft 1 m),
      allN m fun i => bIf(bitK f i,
        bIf(Nat.beq u (PX i), true, bIf(Nat.beq u (PY i), true, Nat.beq u (PXY i))), true))),
    allN N (fun u => bIf(bitK INV u, strictB (T u) fun x => strictB (FM u) fun f =>
      allN N fun v => bIf(bitK INV v, bIf(Nat.beq u v, true,
        bIf(cmK n w ps x (T v), Nat.blt (nat_lit 0) (Nat.land f (FM v)), true)), true), true))))

end CFSG.KC.FourJ

end
