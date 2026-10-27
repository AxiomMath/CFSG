module

public import Certificates.Data.Kernel.Spor.Chain
public import Certificates.Data.Kernel.Spor.Mathieu

public section

namespace CFSG.KS.Raw

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu

@[expose] noncomputable def rcnt (R : Nat) : Nat := Nat.land R (nat_lit 65535)

@[expose] noncomputable def rpt (w m R k : Nat) : Nat := fld(R, Nat.add (nat_lit 16) (Nat.mul w k), m)

@[expose] noncomputable def rpos (w m nw R z : Nat) : Nat :=
  fld(R, Nat.add (Nat.add (nat_lit 16) nw) (Nat.mul w z), m)

@[expose] noncomputable def rpar (w m nw R k : Nat) : Nat :=
  fld(R, Nat.add (Nat.add (nat_lit 16) (Nat.add nw nw)) (Nat.mul w k), m)

@[expose] noncomputable def rlab (_n nw R k : Nat) : Nat :=
  fld(R, Nat.add (Nat.add (nat_lit 16) (Nat.add nw (Nat.add nw nw))) (Nat.mul (nat_lit 8) k),
    nat_lit 255)

@[expose] noncomputable def roff (n nw R : Nat) : Nat :=
  fld(R, Nat.add (Nat.add (nat_lit 16) (Nat.add nw (Nat.add nw nw))) (Nat.mul (nat_lit 8) n),
    nat_lit 4294967295)

@[expose] noncomputable def letterK (S SI : Nat → Nat) (kS l : Nat) : Nat :=
  nIf(Nat.blt l kS, S l, SI (Nat.sub l kS))

@[expose] noncomputable def fixMaskK (w m : Nat) (S : Nat → Nat) (kS BP i : Nat) : Nat :=
  foldUp kS (fun j M => nIf(allN i (fun t => strictB (pg w m BP t) (fun b =>
      Nat.beq (pg w m (S j) b) b)),
    Nat.lor M (Nat.shiftLeft (nat_lit 1) j), M)) (nat_lit 0)

@[expose] noncomputable def stepTab (kS M : Nat) : Nat :=
  foldUp (Nat.add kS kS) (fun l s => strictN (Nat.land s (nat_lit 255)) (fun c =>
      nIf(hasBit M (nIf(Nat.blt l kS, l, Nat.sub l kS)),
        Nat.add (Nat.succ s) (Nat.shiftLeft l (Nat.add (nat_lit 8) (Nat.mul (nat_lit 8) c))), s)))
    (nat_lit 0)

@[expose] noncomputable def stCnt (T : Nat) : Nat := Nat.land T (nat_lit 255)

@[expose] noncomputable def stAt (T j : Nat) : Nat :=
  fld(T, Nat.add (nat_lit 8) (Nat.mul (nat_lit 8) j), nat_lit 255)

@[expose] noncomputable def lexLtK (a b c d : Nat) : Bool :=
  bIf(Nat.blt a c, true, bAnd(Nat.beq a c, Nat.blt b d))

@[expose] noncomputable def szOK (n w : Nat) : Bool :=
  bAnd(Nat.blt n (nat_lit 16777216), Nat.blt (Nat.succ n) (Nat.shiftLeft (nat_lit 1) w))

@[expose] noncomputable def levelK (n w m nw _pm idn : Nat) (S SI TR TRI : Nat → Nat)
    (kS root T R : Nat) : Bool :=
  bAnd(szOK n w, bAnd(Nat.blt kS (nat_lit 128),
  strictB (rcnt R) (fun c => strictB (stCnt T) (fun r => strictB (roff n nw R) (fun o =>
  bAnd(Nat.blt (nat_lit 0) c, bAnd(Nat.ble c n, bAnd(Nat.blt r (nat_lit 256),
  bAnd(Nat.beq (rpt w m R (nat_lit 0)) root,
  bAnd(allN c (fun k => strictB (rpt w m R k) (fun p =>
    bAnd(Nat.blt p n, Nat.beq (rpos w m nw R p) k))),
  bAnd(allN n (fun z => strictB (rpos w m nw R z) (fun q =>
    bIf(Nat.blt q c, Nat.beq (rpt w m R q) z, true))),
  bAnd(allN c (fun k => bIf(Nat.beq k (nat_lit 0), true,
    strictB (rpar w m nw R k) (fun pa => strictB (rlab n nw R k) (fun lb =>
    bAnd(Nat.blt pa k, bAnd(Nat.blt lb r,
      Nat.beq (pg w m (letterK S SI kS (stAt T lb)) (rpt w m R pa)) (rpt w m R k))))))),
  bAnd(allN c (fun k => bIf(Nat.beq k (nat_lit 0), true, bIf(Nat.blt (Nat.succ k) c,
    lexLtK (rpar w m nw R k) (rlab n nw R k) (rpar w m nw R (Nat.succ k))
      (rlab n nw R (Nat.succ k)), true))),
  bAnd(allN c (fun h => strictB (rpt w m R h) (fun p => allN r (fun j =>
    strictB (rpos w m nw R (pg w m (letterK S SI kS (stAt T j)) p)) (fun k =>
    bAnd(Nat.blt k c, bIf(Nat.beq k (nat_lit 0), true,
      bIf(lexLtK h j (rpar w m nw R k) (rlab n nw R k), false, true))))))),
  bAnd(Nat.beq (TR o) idn,
  bAnd(allN c (fun k => bIf(Nat.beq k (nat_lit 0), true,
    eq2 n w m (TR (Nat.add o k)) (letterK S SI kS (stAt T (rlab n nw R k)))
      (TR (Nat.add o (rpar w m nw R k))))),
  allN c (fun k => permOK n w m nw (TR (Nat.add o k)) (TRI (Nat.add o k)))))))))))))))))))

@[expose] noncomputable def siftK (n w m nw idn : Nat) (LR TRI : Nat → Nat) (BP : Nat) (f : Nat) :
    Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ g => bAnd(szOK n w, Nat.beq g idn))
    (fun _ ih l g => strictB (LR l) (fun R =>
      strictB (rpos w m nw R (pg w m g (pg w m BP l))) (fun k =>
      bIf(Nat.blt k (rcnt R),
        strictB (pcomp n w m (TRI (Nat.add (roff n nw R) k)) g) (ih (Nat.succ l)),
        false))))
    f

@[expose] noncomputable def schK (n w m nw idn : Nat) (S SI LR TR TRI : Nat → Nat)
    (kS BP nb i T h₀ cnt : Nat) : Bool :=
  strictB (LR i) (fun R => strictB (rcnt R) (fun c => strictB (roff n nw R) (fun o =>
  allN cnt (fun dh => strictB (Nat.add h₀ dh) (fun h => bIf(Nat.blt h c,
    strictB (TR (Nat.add o h)) (fun th => strictB (rpt w m R h) (fun p =>
    allN (stCnt T) (fun j => strictB (letterK S SI kS (stAt T j)) (fun s =>
      strictB (rpos w m nw R (pg w m s p)) (fun k => bAnd(Nat.blt k c,
        strictB (pcomp n w m (TRI (Nat.add o k)) (pcomp n w m s th))
          (siftK n w m nw idn LR TRI BP (Nat.sub nb (Nat.succ i)) (Nat.succ i)))))))),
    true))))))

@[expose] noncomputable def wordK (n w m idn : Nat) (S SI : Nat → Nat) (wd : List Int) : Nat :=
  List.rec (motive := fun _ => Nat) idn
    (fun z _ ih => strictN ih (fun T => strictN (icode z) (fun c =>
      pcomp n w m (nIf(Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 0),
        S (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)),
        SI (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)))) T))) wd

@[expose] noncomputable def lettersK (j : Nat) (wd : List Int) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun z _ ih => strictB (icode z) (fun c =>
    bAnd(Nat.blt (nat_lit 0) c, bAnd(Nat.ble (Nat.shiftRight c (nat_lit 1)) j, ih)))) wd

@[expose] noncomputable def dword (D : List (List Int)) (k j : Nat) : List Int :=
  Bool.rec (motive := fun _ => List Int)
    (List.rec (motive := fun _ => Nat → List Int) (fun _ => [])
      (fun x _ ih i => Nat.rec (motive := fun _ => List Int) x (fun i' _ => ih i') i) D
      (Nat.sub j k))
    [] (Nat.blt j k)

@[expose] noncomputable def packB (w : Nat) (B : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun x _ ih => Nat.lor x (Nat.shiftLeft ih w)) B

@[expose] noncomputable def headK (n w m nw idn : Nat) (S SI : Nat → Nat) (kS kO : Nat)
    (D : List (List Int)) (nb BP : Nat) : Bool :=
  bAnd(szOK n w, bAnd(Nat.blt kS (nat_lit 128), bAnd(Nat.ble kO kS, bAnd(Nat.beq (Nat.add (lenW D) kO) kS,
  bAnd(allN kS (fun j => permOK n w m nw (S j) (SI j)),
  bAnd(allN kS (fun j => bIf(Nat.blt j kO, true,
    strictB (S j) (fun sj => bAnd(lettersK j (dword D kO j),
      Nat.beq sj (wordK n w m idn S SI (dword D kO j)))))),
  bAnd(allN kS (fun j => bIf(allN nb (fun t => strictB (pg w m BP t) (fun b =>
      Nat.beq (pg w m (S j) b) b)), Nat.beq (S j) idn, true)),
  allN nb (fun t => Nat.blt (pg w m BP t) n))))))))

end CFSG.KS.Raw

end
