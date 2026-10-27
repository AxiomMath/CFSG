module

public import Certificates.Data.Kernel.SporSch.MathieuCls
public import Certificates.Data.Kernel.SporSch.J1Pt
public import Certificates.Data.Kernel.Spor.Prim

public section

namespace CFSG.KS.SporSch.MBT

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.M11 CFSG.KS.SporSch.MOC

@[expose] noncomputable def walkK (w m X t : Nat) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => nat_lit 0)
    (fun _ ih q c => strictN (pg w m X q) (fun q' =>
      nIf(Nat.beq q' t, Nat.succ c, ih q' (Nat.succ c))))

@[expose] noncomputable def fwdK (n w m BP X i : Nat) : Nat :=
  foldUp i (fun j acc => nIf(Nat.beq acc (nat_lit 0),
    strictN (walkK w m X (pg w m BP i) n (pg w m BP j) (nat_lit 0)) (fun e =>
      nIf(Nat.beq e (nat_lit 0), nat_lit 0,
        Nat.succ (Nat.add j (Nat.mul (nat_lit 64) e)))), acc)) (nat_lit 0)

@[expose] noncomputable def btGo (n w m nw BP : Nat) (LR TR TRI : Nat → Nat) (X Y : Nat) :
    Nat → Nat → Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat)
    (fun _ h _ s => nIf(Nat.beq (pcomp n w m h X) (pcomp n w m Y h), Nat.succ s, s))
    (fun _ ih i h hi s => strictN (LR i) (fun R => strictN (pg w m BP i) (fun b =>
      strictN (roff n nw R) (fun o => strictN (fwdK n w m BP X i) (fun fc =>
      nIf(Nat.beq fc (nat_lit 0),
        strictN (walkK w m X b n b (nat_lit 0)) (fun lb =>
          foldUp (rcnt R) (fun t s => strictN (pg w m h (rpt w m R t)) (fun q =>
            nIf(Nat.beq (walkK w m Y q n q (nat_lit 0)) lb,
              ih (Nat.succ i) (pcomp n w m h (TR (Nat.add o t)))
                (pcomp n w m (TRI (Nat.add o t)) hi) s, s))) s),
        strictN (Nat.pred fc) (fun c =>
          strictN (rpos w m nw R (pg w m hi (itF (fun p => pg w m Y p) (Nat.div c (nat_lit 64))
            (pg w m h (pg w m BP (Nat.mod c (nat_lit 64))))))) (fun t =>
          nIf(Nat.blt t (rcnt R),
            ih (Nat.succ i) (pcomp n w m h (TR (Nat.add o t)))
              (pcomp n w m (TRI (Nat.add o t)) hi) s, s)))))))))

@[expose] noncomputable def btK (n w m nw BP k : Nat) (LR TR TRI : Nat → Nat) (X Y : Nat) : Nat :=
  btGo n w m nw BP LR TR TRI X Y k (nat_lit 0) (pidn n w) (pidn n w) (nat_lit 0)

@[expose] noncomputable def fixN (n w m x : Nat) : Nat :=
  foldN n (fun i s => nIf(Nat.beq (pg w m x i) i, Nat.succ s, s)) (nat_lit 0)

@[expose] noncomputable def diffK (n w m x y : Nat) : Bool :=
  bIf(Nat.beq (ordC n w m x) (ordC n w m y), bIf(Nat.beq (fixN n w m x) (fixN n w m y),
    bIf(Nat.beq (fixN n w m (pcomp n w m x x)) (fixN n w m (pcomp n w m y y)), false, true),
    true), true)

@[expose] noncomputable def repK (n w m nw BP k : Nat) (LR TR TRI : Nat → Nat) (X C : Nat) : Bool :=
  bAnd(canonK n w m nw X, bAnd(siftK n w m nw (pidn n w) LR TRI BP k (nat_lit 0) X,
    bAnd(Nat.blt (nat_lit 1) (ordC n w m X), Nat.beq (btK n w m nw BP k LR TR TRI X X) C)))

@[expose] noncomputable def distK (n w m nw BP k : Nat) (LR TR TRI : Nat → Nat) (X Y : Nat) :
    Bool :=
  bIf(diffK n w m X Y, true, Nat.beq (btK n w m nw BP k LR TR TRI X Y) (nat_lit 0))

@[expose] noncomputable def sumAllK (N : Nat) (CL : List Nat) (len : Nat) : Nat :=
  foldN len (fun i s => Nat.add s (Nat.div N (CL.getD i (nat_lit 1)))) (nat_lit 0)

@[expose] noncomputable def sumOrdK (n w m N : Nat) (XL CL : List Nat) (mo len : Nat) : Nat :=
  foldN len (fun i s => nIf(Nat.beq (ordC n w m (XL.getD i (nat_lit 0))) mo,
    Nat.add s (Nat.div N (CL.getD i (nat_lit 1))), s)) (nat_lit 0)

@[expose] noncomputable def zTotK (n w m N : Nat) (XL CL : List Nat) (SC : List (List (List Nat)))
    (r len : Nat) : Nat :=
  foldN len (fun i s => nIf(Nat.beq (ordC n w m (XL.getD i (nat_lit 0))) r,
    Nat.add s (Nat.mul (Nat.div N (CL.getD i (nat_lit 1)))
      (((SC.getD i []).map List.sum).sum)), s)) (nat_lit 0)

@[expose] noncomputable def yPtK (w m x e Z i : Nat) : Nat := fpow (pg w m x) e (pg w m Z i)

@[expose] noncomputable def zFixK (n w m e my Z x : Nat) : Bool :=
  bIf(Nat.blt (nat_lit 1) n,
    bAnd(Nat.beq (fpow (yPtK w m x e Z) my (nat_lit 0)) (nat_lit 0),
      Nat.beq (fpow (yPtK w m x e Z) my (nat_lit 1)) (nat_lit 1)), true)

@[expose] noncomputable def zTest (n w m idn mx my : Nat) (ws : List (List Nat × Nat)) (Z x : Nat) :
    Bool :=
  bAnd(zFixK n w m (Nat.sub mx (nat_lit 1)) my Z x,
    strictB (pcomp n w m (powK n w m idn x (Nat.sub mx (nat_lit 1))) Z) (fun y =>
      bAnd(ordIs n w m idn y (Nat.sub my (nat_lit 1)), wordOrdK n w m idn mx my ws x y)))

@[expose] noncomputable def cntZK (n w m idn mx my : Nat) (ws : List (List Nat × Nat)) (Z : Nat)
    (d : ClsD) (lo len : Nat) : Nat :=
  foldUp len (fun l c => strictN (Nat.add lo l) (fun k =>
    nIf(Nat.blt k d.c, nIf(zTest n w m idn mx my ws Z (d.ST k), Nat.succ c, c), c))) (nat_lit 0)

end CFSG.KS.SporSch.MBT

end
