module

public import Certificates.Data.Kernel.SporSch.PairCl
public import Certificates.Data.Kernel.Spor.Raw
public import Certificates.Data.Kernel.Spor.Prim

public section

namespace CFSG.KS.Suz27216

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.KS.Mathieu CFSG.KS.Prim

@[expose] noncomputable def notK (b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) true false b

@[expose] noncomputable def wptK (w : Nat) (G : Nat → Nat) (wd : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) x (fun j _ ih => pg w (mask w) (G j) ih) wd

@[expose] noncomputable def memL (x : Nat) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun y _ ih => bIf(Nat.beq x y, true, ih)) L

@[expose] noncomputable def fixOK (n w : Nat) (G : Nat → Nat) (W : List (List Nat)) (b : Nat)
    (F : List Nat) : Bool :=
  bAnd(List.rec (motive := fun _ => Bool) true
      (fun wd _ ih => bAnd(Nat.beq (wptK w G wd b) b, ih)) W,
    allN n (fun q => bIf(memL q F, true,
      List.rec (motive := fun _ => Bool) false
        (fun wd _ ih => bIf(Nat.beq (wptK w G wd q) q, ih, true)) W)))

@[expose] noncomputable def chainK (n w : Nat) (LR TR : Nat → Nat) : Bool :=
  strictB (Nat.mul n w) (fun nw =>
  bAnd(allN (nat_lit 3) (fun i => Nat.beq (trK n nw LR TR i (nat_lit 0)) (pidn n w)),
  bAnd(allN (rcnt (LR 0)) (fun a =>
    Nat.beq (rpos w (mask w) nw (LR 0) (pg w (mask w) (trK n nw LR TR 0 a) (nat_lit 0))) a),
  bAnd(allN (rcnt (LR 1)) (fun b => strictB (trK n nw LR TR 1 b) (fun B =>
    bAnd(Nat.beq (pg w (mask w) B (nat_lit 0)) (nat_lit 0),
      Nat.beq (rpos w (mask w) nw (LR 1) (pg w (mask w) B (nat_lit 1))) b))),
  allN (rcnt (LR 2)) (fun c => strictB (trK n nw LR TR 2 c) (fun C =>
    bAnd(Nat.beq (pg w (mask w) C (nat_lit 0)) (nat_lit 0),
    bAnd(Nat.beq (pg w (mask w) C (nat_lit 1)) (nat_lit 1),
      Nat.beq (rpos w (mask w) nw (LR 2) (pg w (mask w) C (nat_lit 2))) c))))))))

@[expose] noncomputable def pt3 (w A B C x : Nat) : Nat :=
  pg w (mask w) A (pg w (mask w) B (pg w (mask w) C x))

@[expose] noncomputable def rejK (w : Nat) (G : Nat → Nat) (k A B C : Nat) : Bool :=
  notK (allN k (fun j => strictB (G j) (fun g =>
    Nat.beq (pt3 w A B C (pg w (mask w) g (nat_lit 0))) (pg w (mask w) g (pt3 w A B C (nat_lit 0))))))

@[expose] noncomputable def code3 (p0 p1 p2 : Nat) : Nat :=
  Nat.lor p0 (Nat.lor (Nat.shiftLeft p1 (nat_lit 11)) (Nat.shiftLeft p2 (nat_lit 22)))

@[expose] noncomputable def cent2 (n w : Nat) (LR TR TRI G : Nat → Nat) (k : Nat) (SV F2 : List Nat)
    (A AI B BI p0 p1 : Nat) : Bool :=
  strictB (Nat.mul n w) (fun nw =>
  List.rec (motive := fun _ => Bool) true (fun q _ ih =>
    strictB (pg w (mask w) AI q) (fun u =>
    bAnd(Nat.beq (pg w (mask w) A u) q,
    strictB (pg w (mask w) BI u) (fun y =>
    bAnd(Nat.beq (pg w (mask w) B y) u,
    strictB (rpos w (mask w) nw (LR 2) y) (fun c =>
    bAnd(bIf(Nat.blt c (rcnt (LR 2)),
      bIf(memL (code3 p0 p1 q) SV, true, rejK w G k A B (trK n nw LR TR 2 c)), true), ih))))))) F2)

@[expose] noncomputable def cent1 (n w : Nat) (LR TR TRI G : Nat → Nat) (k : Nat)
    (SV F1 F2 : List Nat) (A AI : Nat) : Bool :=
  strictB (Nat.mul n w) (fun nw => strictB (pg w (mask w) A (nat_lit 0)) (fun p0 =>
  List.rec (motive := fun _ => Bool) true (fun p _ ih =>
    strictB (pg w (mask w) AI p) (fun x =>
    bAnd(Nat.beq (pg w (mask w) A x) p,
    strictB (rpos w (mask w) nw (LR 1) x) (fun b =>
    bAnd(bIf(Nat.blt b (rcnt (LR 1)),
      cent2 n w LR TR TRI G k SV F2 A AI (trK n nw LR TR 1 b) (triK n nw LR TRI 1 b) p0 p, true),
      ih))))) F1))

@[expose] noncomputable def centK (n w : Nat) (LR TR TRI G : Nat → Nat) (k : Nat)
    (SV F1 F2 : List Nat) (lo len : Nat) : Bool :=
  strictB (Nat.mul n w) (fun nw =>
  allN len (fun d => strictB (Nat.add lo d) (fun a =>
    bIf(Nat.blt a (rcnt (LR 0)),
      cent1 n w LR TR TRI G k SV F1 F2 (trK n nw LR TR 0 a) (triK n nw LR TRI 0 a), true))))

@[expose] noncomputable def posOf (n w : Nat) (LR TRI : Nat → Nat) (v : Nat) : Nat :=
  strictN (Nat.mul n w) (fun nw =>
  strictN (rpos w (mask w) nw (LR 0) (Nat.land v (nat_lit 2047))) (fun a =>
  strictN (triK n nw LR TRI 0 a) (fun AI =>
  strictN (rpos w (mask w) nw (LR 1)
    (pg w (mask w) AI (Nat.land (Nat.shiftRight v (nat_lit 11)) (nat_lit 2047)))) (fun b =>
  strictN (rpos w (mask w) nw (LR 2) (pg w (mask w) (triK n nw LR TRI 1 b)
    (pg w (mask w) AI (Nat.shiftRight v (nat_lit 22))))) (fun c =>
  Nat.lor a (Nat.lor (Nat.shiftLeft b (nat_lit 16)) (Nat.shiftLeft c (nat_lit 32))))))))

@[expose] noncomputable def prodOf (n w : Nat) (LR TR : Nat → Nat) (P : Nat) : Nat :=
  strictN (Nat.mul n w) (fun nw =>
  pcomp n w (mask w) (pcomp n w (mask w) (trK n nw LR TR 0 (Nat.land P (nat_lit 65535)))
    (trK n nw LR TR 1 (Nat.land (Nat.shiftRight P (nat_lit 16)) (nat_lit 65535))))
    (trK n nw LR TR 2 (Nat.shiftRight P (nat_lit 32))))

@[expose] noncomputable def evW (w : Nat) (Ws : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) x (fun s _ ih => pg w (mask w) s ih) Ws

@[expose] noncomputable def fixB (w : Nat) (Ws : List Nat) : Bool :=
  bAnd(Nat.beq (evW w Ws (nat_lit 0)) (nat_lit 0),
    bAnd(Nat.beq (evW w Ws (nat_lit 1)) (nat_lit 1), Nat.beq (evW w Ws (nat_lit 2)) (nat_lit 2)))

@[expose] noncomputable def sqB (w s : Nat) : Bool := fixB w [s, s]

@[expose] noncomputable def surv1 (n w : Nat) (msift : Nat → Bool) (T1 v s sI : Nat) : Bool :=
  bAnd(canonK n w (mask w) (Nat.mul n w) s,
  bAnd(permOK n w (mask w) (Nat.mul n w) s sI,
  bAnd(msift s,
  bAnd(Nat.beq (pcomp n w (mask w) s T1) (pcomp n w (mask w) T1 s),
  bAnd(Nat.beq (code3 (pg w (mask w) s (nat_lit 0)) (pg w (mask w) s (nat_lit 1))
      (pg w (mask w) s (nat_lit 2))) v,
    bIf(sqB w s, true, fixB w [s, s, s]))))))

@[expose] noncomputable def surv2 (w s sI t tI : Nat) : Bool :=
  bAnd(fixB w [s, t, sI, tI, s, t, sI, tI],
    bIf(bAnd(sqB w s, sqB w t), fixB w [sI, tI, s, t], true))

@[expose] noncomputable def sqCnt (w : Nat) (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun s _ ih => nIf(sqB w s, Nat.succ ih, ih)) L

@[expose] noncomputable def lenL (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) L

@[expose] noncomputable def mkL (f : Nat → Nat) (L : List Nat) (k : List Nat → Bool) : Bool :=
  List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun k => k [])
    (fun v _ ih k => strictB (f v) (fun s => ih (fun R => k (s :: R)))) L k

@[expose] noncomputable def survK (n w : Nat) (msift : Nat → Bool) (LR TR TRI : Nat → Nat)
    (T1 : Nat) (SV : List Nat) (r : Nat) : Bool :=
  bAnd(Nat.beq (lenL SV) r,
  mkL (fun v => prodOf n w LR TR (posOf n w LR TRI v)) SV (fun LS =>
  mkL (fun s => pinvS n w (mask w) s) LS (fun LI =>
  bAnd(allN r (fun i => surv1 n w msift T1 (nget SV i) (nget LS i) (nget LI i)),
  bAnd(allN r (fun i => allN r (fun j => surv2 w (nget LS i) (nget LI i) (nget LS j) (nget LI j))),
    Nat.ble (sqCnt w LS) (nat_lit 4))))))

@[expose] noncomputable def xK (n w : Nat) (Gi GiI : Nat → Nat) (j : Nat) : Nat :=
  pcomp n w (mask w) (pcomp n w (mask w) (pcomp n w (mask w) (Gi 1) (Gi (Nat.add j 2))) (GiI 1))
    (GiI (Nat.add j 2))

@[expose] noncomputable def xiK (n w : Nat) (Gi GiI : Nat → Nat) (j : Nat) : Nat :=
  pcomp n w (mask w) (pcomp n w (mask w) (pcomp n w (mask w) (Gi (Nat.add j 2)) (Gi 1))
    (GiI (Nat.add j 2))) (GiI 1)

@[expose] noncomputable def letK (n w : Nat) (Gi GiI : Nat → Nat) (c : Nat) : Nat :=
  nIf(Nat.blt c (nat_lit 5), xK n w Gi GiI c, xiK n w Gi GiI (Nat.sub c (nat_lit 5)))

@[expose] noncomputable def wordK (n w : Nat) (Gi GiI : Nat → Nat) (wd : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (pidn n w)
    (fun c _ ih => strictN ih (fun acc => pcomp n w (mask w) (letK n w Gi GiI c) acc)) wd

@[expose] def oddCodes : List (List Nat) :=
  [[5], [0, 4, 4], [5], [0, 3, 4, 8], [3, 5], [0, 3, 9], [8], [5, 6], [4, 1, 0]]

@[expose] def oddExps : List Nat := [3, 5, 3, 7, 5, 7, 5, 3, 3]

@[expose] def zCode : List Nat := [9, 3, 4, 3]

@[expose] noncomputable def ngetL (L : List (List Nat)) (i : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun x _ ih i => Nat.rec (motive := fun _ => List Nat) x (fun i' _ => ih i') i) L i

@[expose] noncomputable def wordsK (n w : Nat) (Gi GiI OW : Nat → Nat) : Bool :=
  bAnd(allN (nat_lit 7) (fun j => bAnd(canonK n w (mask w) (Nat.mul n w) (Gi j),
    permOK n w (mask w) (Nat.mul n w) (Gi j) (GiI j))),
  bAnd(allN (nat_lit 9) (fun k => strictB (OW k) (fun t =>
    bAnd(canonK n w (mask w) (Nat.mul n w) t,
    bAnd(Nat.beq t (wordK n w Gi GiI (ngetL oddCodes k)),
      Nat.beq (ppow n w (mask w) (pidn n w) t (nget oddExps k)) (pidn n w))))),
    Nat.beq (OW (nat_lit 9)) (wordK n w Gi GiI zCode)))

@[expose] noncomputable def inT (cnt : Nat) (T : Nat → Nat) (x : Nat) : Bool :=
  notK (allN cnt (fun q => notK (Nat.beq (T q) x)))

@[expose] noncomputable def rK (n w : Nat) (OW G : Nat → Nat) (cnt : Nat) (T : Nat → Nat) : Bool :=
  strictB (pinvS n w (mask w) (OW (nat_lit 8))) (fun wI =>
  bAnd(permOK n w (mask w) (Nat.mul n w) (OW (nat_lit 8)) wI,
  bAnd(allN (nat_lit 4) (fun j => Nat.beq (G j)
    (pcomp n w (mask w) (OW (Nat.mul 2 j)) (OW (Nat.add (Nat.mul 2 j) 1)))),
  bAnd(inT cnt T (OW (nat_lit 9)),
    allN (nat_lit 4) (fun j =>
      inT cnt T (pcomp n w (mask w) (pcomp n w (mask w) (OW (nat_lit 8)) (G j)) wI))))))

@[expose] noncomputable def hK (n w : Nat) (msift : Nat → Bool) (HP T1 : Nat) (OW G GN : Nat → Nat) :
    Bool :=
  strictB (pinvS n w (mask w) HP) (fun hI =>
  bAnd(canonK n w (mask w) (Nat.mul n w) HP,
  bAnd(permOK n w (mask w) (Nat.mul n w) HP hI,
  bAnd(msift HP,
  bAnd(Nat.beq (pcomp n w (mask w) (pcomp n w (mask w) HP T1) hI) (OW (nat_lit 9)),
    allN (nat_lit 5) (fun j => bAnd(canonK n w (mask w) (Nat.mul n w) (GN j),
      Nat.beq (GN j) (pcomp n w (mask w) (pcomp n w (mask w) hI
        (nIf(Nat.blt j (nat_lit 4), G j, OW (nat_lit 8)))) HP))))))))

end CFSG.KS.Suz27216

end
