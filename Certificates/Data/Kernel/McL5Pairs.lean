module

public import Certificates.Data.Kernel.Spor.Prim
public import Certificates.Data.McLFivePairs

public section

namespace CFSG.KS.McL5P

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim

@[expose] noncomputable def cj (r ri x : Nat) : Nat :=
  pcomp (nat_lit 275) (nat_lit 9) (mask (nat_lit 9))
    (pcomp (nat_lit 275) (nat_lit 9) (mask (nat_lit 9)) ri x) r

@[expose] noncomputable def l4 (a b c d l : Nat) : Nat :=
  nIf(Nat.beq l (nat_lit 0), a, nIf(Nat.beq l (nat_lit 1), b, nIf(Nat.beq l (nat_lit 2), c, d)))

@[expose] noncomputable def perm275 (p q : Nat) : Bool :=
  permOK (nat_lit 275) (nat_lit 9) (mask (nat_lit 9)) (Nat.mul (nat_lit 275) (nat_lit 9)) p q

@[expose] noncomputable def wEq (S SI : Nat → Nat) (k : Nat) (wd : List Int) (r : Nat) : Bool :=
  wordEqK (nat_lit 275) (nat_lit 9) (mask (nat_lit 9)) (pidn (nat_lit 275) (nat_lit 9)) S SI k wd r

@[expose] noncomputable def pairK1 (GA GB U V UI VI : Nat) (REP REPI : Nat → Nat)
    (e : Nat × List Int × List Int) : Bool :=
  bAnd(Nat.blt e.1 (nat_lit 114), strictB (REP e.1) (fun r => strictB (REPI e.1) (fun ri =>
    strictB (cj r ri U) (fun c1 => strictB (cj r ri V) (fun c2 =>
      strictB (cj r ri UI) (fun c1i => strictB (cj r ri VI) (fun c2i =>
        bAnd(perm275 c1 c1i, bAnd(perm275 c2 c2i,
          bAnd(wEq (l4 U V c1 c2) (l4 UI VI c1i c2i) (nat_lit 4) e.2.1 GA,
            wEq (l4 U V c1 c2) (l4 UI VI c1i c2i) (nat_lit 4) e.2.2 GB))))))))))

@[expose] noncomputable def actK (NG NGI BK BKI : Nat → Nat)
    (e : Nat × Nat × Nat × List (List Int)) : Bool :=
  bAnd(Nat.blt e.1 (nat_lit 3), bAnd(Nat.blt e.2.1 (nat_lit 4), bAnd(Nat.blt e.2.2.1 (nat_lit 3),
    bAnd(Nat.beq e.2.2.2.length (nat_lit 4),
      allN (nat_lit 4) (fun l => wEq (fun t => BK (Nat.add (Nat.mul (nat_lit 4) e.2.2.1) t))
        (fun t => BKI (Nat.add (Nat.mul (nat_lit 4) e.2.2.1) t)) (nat_lit 4) (e.2.2.2.getD l [])
        (cj (NG e.2.1) (NGI e.2.1) (BK (Nat.add (Nat.mul (nat_lit 4) e.1) l))))))))

@[expose] noncomputable def l8 (BK : Nat → Nat) (i j t : Nat) : Nat :=
  nIf(Nat.blt t (nat_lit 4), BK (Nat.add (Nat.mul (nat_lit 4) i) t),
    BK (Nat.add (Nat.mul (nat_lit 4) j) (Nat.sub t (nat_lit 4))))

@[expose] noncomputable def joinK (GA GB : Nat) (BK BKI : Nat → Nat)
    (e : Nat × Nat × List Int × List Int) : Bool :=
  bAnd(Nat.blt e.1 (nat_lit 3), bAnd(Nat.blt e.2.1 (nat_lit 3),
    bAnd(wEq (l8 BK e.1 e.2.1) (l8 BKI e.1 e.2.1) (nat_lit 8) e.2.2.1 GA,
      wEq (l8 BK e.1 e.2.1) (l8 BKI e.1 e.2.1) (nat_lit 8) e.2.2.2 GB)))

@[expose] noncomputable def blkK (HK HKI B0 BK BKI : Nat → Nat) : Bool :=
  allN (nat_lit 3) (fun k => allN (nat_lit 4) (fun l =>
    bAnd(Nat.beq (BK (Nat.add (Nat.mul (nat_lit 4) k) l)) (cj (HK k) (HKI k) (B0 l)),
      perm275 (BK (Nat.add (Nat.mul (nat_lit 4) k) l)) (BKI (Nat.add (Nat.mul (nat_lit 4) k) l)))))

@[expose] def dW : List (List Int) := Certificates.McLFivePairs.sgsWords.drop 4

end CFSG.KS.McL5P

end
