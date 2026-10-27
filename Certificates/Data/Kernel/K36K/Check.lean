module

public import Certificates.Data.K36SporPlanes
public import Certificates.Data.Kernel.MaxD2.Check

public section

namespace CFSG.KS.K36K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MaxD2 Certificates.K36Spor

@[expose] noncomputable def centEK (n w z v g f1 f2 : Nat) : Bool :=
  strictB (pcomp n w (mask w) (pw n w z f1) (pw n w v f2)) (fun y =>
    bAnd(bIf(Nat.beq y (pidn n w), false, true),
      Nat.beq (pcomp n w (mask w) g y) (pcomp n w (mask w) y g)))

@[expose] noncomputable def centCK (n w : Nat) (S : SData) (EG : Nat → Nat) (c : Cent) (g : Nat) :
    Bool :=
  bAnd(Nat.blt c.idx S.ys.length, bAnd(Nat.blt (S.ys.getD c.idx (nat_lit 0)) S.base.eW.length,
    centEK n w (EG (nat_lit 0)) (EG (S.ys.getD c.idx (nat_lit 0))) g c.f1 c.f2))

@[expose] noncomputable def centSK (n w : Nat) (S : SData) (EG GT : Nat → Nat) : Bool :=
  bAnd(Nat.beq S.gc.length S.base.gWs.length,
    allN S.base.gWs.length (fun j => centCK n w S EG (S.gc.getD j default) (GT j)))

@[expose] noncomputable def wordsSK (n w : Nat) (S : SData) (GP GT GTI : Nat → Nat) : Bool :=
  allN S.gen.length (fun k =>
    bAnd(wordEqK n w (mask w) (pidn n w) GT GTI S.base.gWs.length (S.wAs.getD k []) (GP (nat_lit 0)),
    bAnd(wordEqK n w (mask w) (pidn n w) GT GTI S.base.gWs.length (S.wBs.getD k []) (GP (nat_lit 1)),
    bAnd((S.wAs.getD k []).all (fun l => allowedS S (S.gen.getD k (nat_lit 0)) (l.natAbs - 1)),
      (S.wBs.getD k []).all (fun l => allowedS S (S.gen.getD k (nat_lit 0)) (l.natAbs - 1))))))

@[expose] noncomputable def cyT (m : Nat) (CT : Nat → Nat) (y l : Nat) : Nat :=
  nIf(Nat.blt l m, CT l, y)

@[expose] noncomputable def excWK (n w : Nat) (S : SData) (X : Exc) (EG GP GPI CT CTI : Nat → Nat)
    (YT YTI : Nat) (FT FYT : Nat → Nat) : Bool :=
  bAnd(Nat.beq X.cc.length X.cW.length,
  bAnd(allN X.cW.length (fun l =>
      bAnd(wordEqK n w (mask w) (pidn n w) GP GPI (nat_lit 2) (X.cW.getD l []) (CT l),
      bAnd(permOK n w (mask w) (Nat.mul n w) (CT l) (CTI l),
      bAnd(Nat.beq (X.cc.getD l default).idx X.idx, centCK n w S EG (X.cc.getD l default) (CT l))))),
  bAnd(wordEqK n w (mask w) (pidn n w) GP GPI (nat_lit 2) X.yW YT,
  bAnd(permOK n w (mask w) (Nat.mul n w) YT YTI,
  bAnd(allN (nat_lit 2) (fun k =>
      bAnd(wordEqK n w (mask w) (pidn n w) CT CTI X.cW.length (X.fWc.getD k []) (FT k),
      bAnd(wordEqK n w (mask w) (pidn n w) CT CTI X.cW.length (X.fyWc.getD k []) (FYT k),
      bAnd(canonK n w (mask w) (Nat.mul n w) (FT k), bAnd(canonK n w (mask w) (Nat.mul n w) (FYT k),
        Nat.beq (pcomp n w (mask w) YT (FT k)) (pcomp n w (mask w) (FYT k) YT)))))),
  bAnd(wordEqK n w (mask w) (pidn n w) (cyT X.cW.length CT YT) (cyT X.cW.length CTI YTI)
      (Nat.succ X.cW.length) X.wA (GP (nat_lit 0)),
    wordEqK n w (mask w) (pidn n w) (cyT X.cW.length CT YT) (cyT X.cW.length CTI YTI)
      (Nat.succ X.cW.length) X.wB (GP (nat_lit 1))))))))

@[expose] noncomputable def ltsK (k : Nat) (wd : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun j _ ih => bAnd(Nat.blt j k, ih)) wd

@[expose] noncomputable def wptK (w : Nat) (F : Nat → Nat) (wd : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) x (fun j _ ih => strictN ih (fun y => pg w (mask w) (F j) y)) wd

@[expose] noncomputable def ptK (w kF : Nat) (F : Nat → Nat) (o0 j : Nat) (wd : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) (allN kF (fun k => Nat.beq (pg w (mask w) (F k) j) j))
    (fun _ _ _ => bAnd(ltsK kF wd, bAnd(Nat.beq (wptK w F wd o0) o0,
      bIf(Nat.beq (wptK w F wd j) j, false, true)))) wd

@[expose] noncomputable def fixWK (n w kF : Nat) (F : Nat → Nat) (k0 o0 : Nat) (HW : List (List Nat))
    (OL : List Nat) (OW : List (List Nat)) : Bool :=
  bAnd(Nat.blt o0 n, bAnd(Nat.blt k0 kF,
  bAnd(bIf(Nat.beq (pg w (mask w) (F k0) o0) o0, false, true),
  bAnd(allN n (fun j => bIf(Nat.beq j o0, true, ptK w kF F o0 j (HW.getD j []))),
  bAnd(Nat.beq OW.length OL.length,
    allN OL.length (fun i => bAnd(ltsK kF (OW.getD i []),
      Nat.beq (wptK w F (OW.getD i []) o0) (OL.getD i (nat_lit 0)))))))))

end CFSG.KS.K36K

end
