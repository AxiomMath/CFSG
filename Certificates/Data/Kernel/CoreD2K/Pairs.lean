module

public import Certificates.Data.Kernel.CoreD2K.Check

public section

namespace CFSG.KS.CoreD2K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MaxD2 Certificates.CoreD2Perm

@[expose] noncomputable def pairPK (n w p ne : Nat) (EG : Nat → Nat) (q : Nat × Nat) : Bool :=
  bAnd(Nat.blt q.1 ne, bAnd(Nat.blt q.2 ne,
    strictB (EG q.1) (fun u => strictB (EG q.2) (fun v =>
      bAnd(Nat.beq (pw n w u p) (pidn n w), bAnd(bIf(Nat.beq u (pidn n w), false, true),
      bAnd(Nat.beq (pcomp n w (mask w) u v) (pcomp n w (mask w) v u), vK n w p u v)))))))

@[expose] noncomputable def fusK (n w : Nat) (D : Data) (EG GT : Nat → Nat) : Bool :=
  bAnd(Nat.beq D.fd.length D.gWs.length,
    allN D.gWs.length (fun j => bAnd(Nat.blt (D.fd.getD j default).pair D.pairs.length,
      kindK n w D.p (EG (D.pairs.getD (D.fd.getD j default).pair (nat_lit 0, nat_lit 0)).1)
        (EG (D.pairs.getD (D.fd.getD j default).pair (nat_lit 0, nat_lit 0)).2) (GT j)
        (nat_lit 0) (D.fd.getD j default).α (D.fd.getD j default).β (D.fd.getD j default).γ
        (D.fd.getD j default).δ)))

@[expose] noncomputable def pairsK (n w : Nat) (D : Data) (GP EG GT GTI : Nat → Nat) : Bool :=
  bAnd(allN D.pairs.length (fun i =>
      pairPK n w D.p D.eW.length EG (D.pairs.getD i (nat_lit 0, nat_lit 0))),
  bAnd(fusK n w D EG GT,
  bAnd(wordEqK n w (mask w) (pidn n w) GT GTI D.gWs.length D.wA (GP (nat_lit 0)),
    wordEqK n w (mask w) (pidn n w) GT GTI D.gWs.length D.wB (GP (nat_lit 1)))))

@[expose] noncomputable def normK (n w p ne : Nat) (EG : Nat → Nat) (f1 f2 f3 f4 : Nat) : Bool :=
  bAnd(Nat.beq ne (nat_lit 3),
  bAnd(Nat.beq (pw n w (EG (nat_lit 0)) p) (pidn n w),
  bAnd(Nat.beq (pw n w (EG (nat_lit 1)) p) (pidn n w),
  bAnd(Nat.beq (pw n w (EG (nat_lit 2)) p) (pidn n w),
  bAnd(Nat.beq (pcomp n w (mask w) (EG (nat_lit 0)) (EG (nat_lit 2)))
      (pcomp n w (mask w) (EG (nat_lit 2)) (EG (nat_lit 0))),
    kindK n w p (EG (nat_lit 0)) (EG (nat_lit 2)) (EG (nat_lit 1)) (nat_lit 0) f1 f2 f3 f4)))))

end CFSG.KS.CoreD2K

end
