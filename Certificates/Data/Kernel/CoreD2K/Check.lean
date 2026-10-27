module

public import Certificates.Data.CoreD2Lines
public import Certificates.Data.Kernel.MaxD2.Check

public section

namespace CFSG.KS.CoreD2K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MaxD2 Certificates.CoreD2Perm

@[expose] noncomputable def gensK (n w : Nat) (V : VData) (GP GPI EG GT GTI : Nat → Nat) : Bool :=
  bAnd(allN (nat_lit 2) (fun j => permOK n w (mask w) (Nat.mul n w) (GP j) (GPI j)),
  bAnd(allN V.base.eW.length (fun k =>
      bAnd(wordEqK n w (mask w) (pidn n w) GP GPI (nat_lit 2) (V.base.eW.getD k []) (EG k),
        canonK n w (mask w) (Nat.mul n w) (EG k))),
    allN V.base.gWs.length (fun j =>
      bAnd(wordEqK n w (mask w) (pidn n w) GP GPI (nat_lit 2) (V.base.gWs.getD j []) (GT j),
        permOK n w (mask w) (Nat.mul n w) (GT j) (GTI j)))))

@[expose] noncomputable def nabK (n w ne : Nat) (EG : Nat → Nat) : Bool :=
  bIf(allN ne (fun i => strictB (EG i) (fun x => allN ne (fun j => strictB (EG j) (fun y =>
    Nat.beq (pcomp n w (mask w) x y) (pcomp n w (mask w) y x))))), false, true)

@[expose] noncomputable def cenK (n w p ne : Nat) (EG : Nat → Nat) : Bool :=
  strictB (EG (nat_lit 0)) (fun z =>
  bAnd(Nat.blt (nat_lit 0) ne, bAnd(Nat.beq (pw n w z p) (pidn n w),
  bAnd(bIf(Nat.beq z (pidn n w), false, true),
    allN ne (fun k => strictB (EG k) (fun e =>
      Nat.beq (pcomp n w (mask w) z e) (pcomp n w (mask w) e z)))))))

@[expose] noncomputable def vK (n w p z v : Nat) : Bool :=
  bAnd(Nat.beq (pw n w v p) (pidn n w), allN p (fun k => bIf(Nat.beq v (pw n w z k), false, true)))

@[expose] noncomputable def cosK (n w z x : Nat) : Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ ih t => bAnd(bIf(Nat.beq x t, false, true), strictB (pcomp n w (mask w) z t) ih))

@[expose] noncomputable def outL (n w p z v x : Nat) : Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ ih t => bAnd(cosK n w z x p t, strictB (pcomp n w (mask w) v t) ih))

@[expose] noncomputable def outK (n w p z v x : Nat) : Bool := outL n w p z v x p (pidn n w)

@[expose] noncomputable def linesK (n w p : Nat) (V : VData) (EG : Nat → Nat) : Bool :=
  strictB (EG (nat_lit 0)) (fun z =>
  bAnd(Nat.beq V.ys.length (Nat.succ p),
  bAnd(allN V.ys.length (fun i => bAnd(Nat.blt (V.ys.getD i (nat_lit 0)) V.base.eW.length,
      vK n w p z (EG (V.ys.getD i (nat_lit 0))))),
    allN V.ys.length (fun j => strictB (EG (V.ys.getD j (nat_lit 0))) (fun x =>
      allN j (fun i => outK n w p z (EG (V.ys.getD i (nat_lit 0))) x))))))

@[expose] noncomputable def kindK (n w p u v g kind f1 f2 f3 f4 : Nat) : Bool :=
  strictB (pcomp n w (mask w) (pw n w u f1) (pw n w v f2)) (fun y =>
  bIf(Nat.beq kind (nat_lit 0),
    bAnd(Nat.beq (pcomp n w (mask w) g u) (pcomp n w (mask w) y g),
      Nat.beq (pcomp n w (mask w) g v)
        (pcomp n w (mask w) (pcomp n w (mask w) (pw n w u f3) (pw n w v f4)) g)),
    bAnd(bIf(Nat.beq y (pidn n w), false, true), bAnd(Nat.beq (pw n w y p) (pidn n w),
      Nat.beq (pcomp n w (mask w) g y) (pcomp n w (mask w) (pw n w y f3) g)))))

@[expose] noncomputable def kindsK (n w : Nat) (V : VData) (EG GT : Nat → Nat) : Bool :=
  bAnd(Nat.beq V.gk.length V.base.gWs.length,
    allN V.base.gWs.length (fun j => bAnd(Nat.blt (V.gk.getD j default).idx V.ys.length,
      kindK n w V.base.p (EG (nat_lit 0)) (EG (V.ys.getD (V.gk.getD j default).idx (nat_lit 0)))
        (GT j) (V.gk.getD j default).kind (V.gk.getD j default).f1 (V.gk.getD j default).f2
        (V.gk.getD j default).f3 (V.gk.getD j default).f4)))

@[expose] noncomputable def wordsK (n w : Nat) (V : VData) (GP GT GTI : Nat → Nat) : Bool :=
  bAnd(Nat.beq V.wAs.length V.ys.length, bAnd(Nat.beq V.wBs.length V.ys.length,
    allN V.ys.length (fun i =>
      bAnd(wordEqK n w (mask w) (pidn n w) GT GTI V.base.gWs.length (V.wAs.getD i [])
          (GP (nat_lit 0)),
      bAnd(wordEqK n w (mask w) (pidn n w) GT GTI V.base.gWs.length (V.wBs.getD i [])
          (GP (nat_lit 1)),
      bAnd(wordOK V i (V.wAs.getD i []), wordOK V i (V.wBs.getD i [])))))))

end CFSG.KS.CoreD2K

end
