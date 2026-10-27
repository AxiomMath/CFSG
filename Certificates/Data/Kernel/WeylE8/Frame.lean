module

public import Certificates.Data.Kernel.WeylE8.Coord

public section

namespace CFSG.KLC.E8

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def e8 (P i : Nat) : Nat := pg (nat_lit 8) (nat_lit 255) P i

@[expose] noncomputable def beqB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) (notB' b) b a

@[expose] noncomputable def norm8K (RK : Nat → Nat) : Bool :=
  allN (nat_lit 240) fun i => strictB (RK i) fun x =>
    Nat.beq (Nat.add (sumN (nat_lit 8) fun k => Nat.mul (cf x k) (cf x k)) (nat_lit 32))
      (Nat.add (Nat.mul (nat_lit 4) (sumN (nat_lit 8) fun k => cf x k)) (nat_lit 8))

@[expose] noncomputable def maskK (NEG KP T : Nat) : Nat :=
  sumN (nat_lit 8) fun i => strictN (e8 KP i) fun p =>
    nIf(Nat.beq (e8 T p) (e8 NEG p), Nat.shiftLeft (nat_lit 1) i, nat_lit 0)

@[expose] noncomputable def inFrame (NEG KP r : Nat) : Bool :=
  notB' (allN (nat_lit 8) fun i => strictB (e8 KP i) fun p =>
    bAnd(notB' (Nat.beq r p), notB' (Nat.beq r (e8 NEG p))))

@[expose] noncomputable def distFr (NEG KP : Nat) : Bool :=
  allN (nat_lit 8) fun i => allN (nat_lit 8) fun j => bIf(Nat.beq i j, true,
    bAnd(notB' (Nat.beq (e8 KP i) (e8 KP j)), notB' (Nat.beq (e8 KP i) (e8 NEG (e8 KP j)))))

@[expose] noncomputable def f16K (RT FT : Nat → Nat) (NEG KP : Nat) : Bool :=
  bAnd(allN (nat_lit 240) (fun r => bIf(inFrame NEG KP r, true, strictB (low (RT r)) fun A =>
      allN (nat_lit 256) fun m => notB' (Nat.beq A (low (FT m))))),
    distFr NEG KP)

@[expose] noncomputable def inList (P n r : Nat) : Bool :=
  notB' (allN n fun j => notB' (Nat.beq r (e8 P j)))

@[expose] noncomputable def negSetK (NEG T P n : Nat) : Bool :=
  bAnd(allN (nat_lit 240) (fun r => beqB (Nat.beq (e8 T r) (e8 NEG r)) (inList P n r)),
    allN n fun j => allN j fun k => notB' (Nat.beq (e8 P j) (e8 P k)))

@[expose] noncomputable def planeK (m : Nat) : Bool :=
  notB' (allN (nat_lit 14) fun j => notB' (Nat.beq m (pg (nat_lit 8) (nat_lit 255)
    (nat_lit 4884001405905638983215069735432975) j)))

@[expose] noncomputable def frameK (RT FT : Nat → Nat) (NEG KP FP : Nat) : Bool :=
  bAnd(allN (nat_lit 240) (fun r => strictB (RT r) fun T =>
      beqB (Nat.beq (low T) (low (FT (maskK NEG KP T)))) (inList FP (nat_lit 16) r)),
  bAnd(allN (nat_lit 256) (fun m => strictB (FT m) fun T => bAnd(Nat.beq (maskK NEG KP T) m,
      allN (nat_lit 8) fun i => strictB (e8 KP i) fun p => Nat.beq (e8 T p)
        (nIf(Nat.beq (Nat.land (Nat.shiftRight m i) (nat_lit 1)) (nat_lit 1), e8 NEG p, p)))),
  bAnd(allN (nat_lit 8) (fun i => strictB (e8 KP i) fun p =>
      negSetK NEG (RT p) (Nat.add p (Nat.shiftLeft (e8 NEG p) (nat_lit 8))) (nat_lit 2)),
  bAnd(allN (nat_lit 8) (fun i => allN i fun j => strictB (e8 KP i) fun p => strictB (e8 KP j) fun q =>
      negSetK NEG (FT (Nat.add (Nat.shiftLeft (nat_lit 1) i) (Nat.shiftLeft (nat_lit 1) j)))
        (Nat.add (Nat.add p (Nat.shiftLeft (e8 NEG p) (nat_lit 8)))
          (Nat.add (Nat.shiftLeft q (nat_lit 16)) (Nat.shiftLeft (e8 NEG q) (nat_lit 24)))) (nat_lit 4)),
    allN (nat_lit 256) (fun m => bIf(Nat.beq (pop8 m) (nat_lit 4),
      beqB (Nat.beq (fixCntK (nat_lit 240) (nat_lit 8) (FT m)) (nat_lit 24)) (planeK m), true))))))

@[expose] noncomputable def ppow (p k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (pidn (nat_lit 240) (nat_lit 8))
    (fun _ ih => strictN ih fun q => pcomp (nat_lit 240) (nat_lit 8) (nat_lit 255) p q) k

@[expose] noncomputable def singerK (ST LR TRI : Nat → Nat) (BP NEG KP SG SGI SL FL : Nat) : Bool :=
  bAnd(permOK (nat_lit 240) (nat_lit 8) (nat_lit 255) (nat_lit 1920) SG SGI,
  bAnd(Nat.beq (Nat.shiftRight SG (nat_lit 1920)) (nat_lit 0),
  bAnd(siftK (nat_lit 240) (nat_lit 8) (mask (nat_lit 8)) (nat_lit 1920) (pidn (nat_lit 240) (nat_lit 8))
      LR TRI BP (nat_lit 8) (nat_lit 0) SG,
  bAnd(Nat.beq (ppow SG (nat_lit 7)) (pidn (nat_lit 240) (nat_lit 8)),
  bAnd(allN (nat_lit 8) (fun i => bAnd(Nat.blt (e8 SL i) (nat_lit 8),
      Nat.beq (e8 SG (e8 KP i)) (e8 KP (e8 SL i)))),
    allN (nat_lit 8) fun i => strictB (e8 KP i) fun p => bIf(Nat.blt i (nat_lit 4),
      bAnd(Nat.blt (e8 FL i) (nat_lit 8), Nat.beq (e8 (ST (nat_lit 5)) p) (e8 NEG (e8 KP (e8 FL i)))),
      Nat.beq (e8 (ST (nat_lit 5)) p) p))))))

end CFSG.KLC.E8

end
