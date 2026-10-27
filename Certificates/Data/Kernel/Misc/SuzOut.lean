module

public import Certificates.Data.Kernel.Misc.TitsPrim

public section

namespace CFSG.KC.SuzOut

open CFSG.KC.Enum CFSG.KS CFSG.KC.IntLines CFSG.KC.LQT.Cov CFSG.KC.TitsPrim

@[expose] noncomputable def repsK (n m : Nat) (L R : Nat → Nat) : Bool :=
  allN m (fun j => strictB (R j) (fun r => bAnd(Nat.blt r n, Nat.beq (L r) j)))

@[expose] noncomputable def blockPt (n w m wT G T : Nat) (L : Nat → Nat) (x : Nat) : Bool :=
  strictB (pg w (mask w) G x) (fun y => bAnd(Nat.blt y n, strictB (L x) (fun l =>
    bIf(Nat.blt l m, bAnd(Nat.blt (L y) m, Nat.beq (L y) (pg wT (mask wT) T l)),
      bIf(Nat.blt (L y) m, false, true)))))

@[expose] noncomputable def blockRep (n w wT G T : Nat) (L R : Nat → Nat) (j : Nat) : Bool :=
  strictB (R j) (fun r => bAnd(Nat.blt r n, Nat.beq (pg wT (mask wT) T j) (L (pg w (mask w) G r))))

@[expose] noncomputable def blockK (n w m wT G T TI : Nat) (L R : Nat → Nat) : Bool :=
  bAnd(allN n (blockPt n w m wT G T L), bAnd(allN m (blockRep n w wT G T L R),
    permOK m wT (mask wT) (Nat.mul m wT) T TI))

@[expose] noncomputable def letInv (S SI : Nat → Nat) (z : Int) : Nat :=
  Int.rec (motive := fun _ => Nat) (fun k => SI (Nat.sub k 1)) (fun k => S k) z

@[expose] noncomputable def ptKI (w : Nat) (S SI : Nat → Nat) (wd : List Int) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun y => y)
    (fun z _ ih y => strictN (pg w (mask w) (letInv S SI z) y) ih) wd

@[expose] noncomputable def letX (w kS : Nat) (S SI : Nat → Nat) (g : List Int) (z : Int)
    (y : Nat) : Nat :=
  Int.rec (motive := fun _ => Nat)
    (fun k => nIf(Nat.beq k (Nat.succ kS), ptK w S SI g y, pg w (mask w) (S (Nat.sub k 1)) y))
    (fun k => nIf(Nat.beq k kS, ptKI w S SI g y, pg w (mask w) (SI k) y)) z

@[expose] noncomputable def ptX (w kS : Nat) (S SI : Nat → Nat) (g : List Int) (wd : List Int)
    (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) x
    (fun z _ ih => strictN ih (fun y => letX w kS S SI g z y)) wd

@[expose] noncomputable def fixX (w kS : Nat) (S : Nat → Nat) (x : Nat) (wd : List Int) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun z _ ih => bAnd(bIf(Nat.beq z.natAbs (Nat.succ kS), true,
      Nat.beq (pg w (mask w) (S (Nat.sub z.natAbs 1)) x) x), ih)) wd

@[expose] noncomputable def reachOK (w kS n x : Nat) (S SI L R : Nat → Nat)
    (T : List (List Char)) (i : Nat) (wd : List Int) : Bool :=
  strictB (Nat.div i n) (fun j => strictB (Nat.mod i n) (fun p =>
    bIf(Nat.beq j (L x), true,
      Option.rec (motive := fun _ => Bool) false
        (fun g => bAnd(CFSG.KS.Raw.lettersK kS g, bAnd(CFSG.KS.Raw.lettersK (Nat.succ kS) wd,
          bAnd(fixX w kS S x wd, Nat.beq (ptX w kS S SI g wd x) p))))
        (intsSK (tokK (List.getD T (R j) []))))))

@[expose] noncomputable def lineWalkK (N : Nat) (ok : Nat → List Int → Bool) :
    List (List Char) → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun i => Nat.beq i N)
    (fun l _ ih i => Option.rec (motive := fun _ => Bool) false
      (fun wd => bAnd(ok i wd, strictB (Nat.succ i) ih)) (intsSK (tokK l)))

@[expose] noncomputable def reachWalkK (w kS n k x : Nat) (S SI L R : Nat → Nat)
    (T H : List (List Char)) : Bool :=
  lineWalkK (Nat.mul k n) (reachOK w kS n x S SI L R T) H (nat_lit 0)

@[expose] noncomputable def bitK (w d r : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i ih => Nat.lor (Nat.shiftLeft (nat_lit 1) (pg w (mask w) r i)) ih) d

@[expose] noncomputable def relK (n w d A : Nat) (M : Nat → Nat) : Bool :=
  allN n (fun x => strictB (bitK w d (M (pg w (mask w) A x))) (fun B =>
    allN d (fun i => strictB (pg w (mask w) (M x) i) (fun y =>
      bAnd(Nat.blt y n, Nat.beq fld(B, pg w (mask w) A y, nat_lit 1) (nat_lit 1))))))

@[expose] noncomputable def moveK (n w d G : Nat) (M : Nat → Nat) (x i : Nat) : Bool :=
  bAnd(Nat.blt x n, bAnd(Nat.blt i d, strictB (pg w (mask w) (M x) i) (fun y =>
    bAnd(Nat.blt y n,
      Nat.beq fld(bitK w d (M (pg w (mask w) G x)), pg w (mask w) G y, nat_lit 1) (nat_lit 0)))))

@[expose] noncomputable def natWalkK (w P N : Nat) : List Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun i => Nat.beq i N)
    (fun x _ ih i => bAnd(Nat.beq x (pg w (mask w) P i), strictB (Nat.succ i) ih))

@[expose] noncomputable def natsPK (w P N : Nat) (cs : List Char) : Bool :=
  Option.rec (motive := fun _ => Bool) false (fun xs => natWalkK w P N xs (nat_lit 0)) (CFSG.KC.LQT.Cov.natsK cs)

@[expose] noncomputable def bodyK (cs : List Char) : List (List Char) :=
  List.dropLast (List.drop 1 (linesK cs))

@[expose] noncomputable def intLinesOK (L : List (List Char)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun l _ ih => bAnd(Option.rec (motive := fun _ => Bool) false (fun _ => true)
      (intsSK (tokK l)), ih)) L

@[expose] noncomputable def wordsK (cs : List Char) : List (List Int) :=
  List.map lineInts (bodyK cs)

end CFSG.KC.SuzOut

end
