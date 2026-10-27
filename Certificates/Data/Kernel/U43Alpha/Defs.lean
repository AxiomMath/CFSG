module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.U43Alpha

open CFSG.KC.Enum

@[expose] noncomputable def cntFix (f : Nat → Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun q ih => nIf(Nat.beq (f q) q, Nat.succ ih, ih)) n

@[expose] noncomputable def labOf (L p : Nat) : Nat := fld(L, Nat.mul (nat_lit 6) p, nat_lit 63)

@[expose] noncomputable def cntLab (L n i : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun q ih => nIf(Nat.beq (labOf L q) i, Nat.succ ih, ih)) n

@[expose] noncomputable def rowOf (R p : Nat) : Nat :=
  fld(R, Nat.mul (nat_lit 24) p, nat_lit 16777215)

@[expose] noncomputable def rowOK (n : Nat) (S : Nat → Nat) (k L R RO nb p : Nat) : Bool :=
  strictB (labOf L p) fun lab => strictB (rowOf R p) fun row =>
    bAnd(Nat.blt lab nb,
    bAnd(bIf(Nat.beq (Nat.shiftRight row (nat_lit 14)) (nat_lit 0),
        bAnd(Nat.beq (Nat.land row (nat_lit 1023)) p,
          Nat.beq (fld(RO, Nat.mul (nat_lit 10) lab, nat_lit 1023)) p),
        strictB (Nat.land row (nat_lit 1023)) fun par =>
        strictB (Nat.land (Nat.shiftRight row (nat_lit 10)) (nat_lit 15)) fun j =>
          bAnd(Nat.blt j k, bAnd(Nat.blt par n,
          bAnd(Nat.beq (pg (nat_lit 10) (nat_lit 1023) (S j) par) p,
          bAnd(Nat.beq (labOf L par) lab,
            Nat.beq (Nat.succ (Nat.shiftRight (rowOf R par) (nat_lit 14)))
              (Nat.shiftRight row (nat_lit 14))))))),
      allN k (fun j => Nat.beq (labOf L (pg (nat_lit 10) (nat_lit 1023) (S j) p)) lab)))

@[expose] noncomputable def orbPart (n : Nat) (S : Nat → Nat) (k L R RO nb SZ : Nat) : Bool :=
  bAnd(allN n (rowOK n S k L R RO nb),
    allN nb (fun i => Nat.beq (cntLab L n i) (fld(SZ, Nat.mul (nat_lit 8) i, nat_lit 255))))

@[expose] noncomputable def fixIn (c : Nat) : Bool :=
  bIf(Nat.beq c (nat_lit 20), true, bIf(Nat.beq c (nat_lit 40), true, Nat.beq c (nat_lit 92)))

@[expose] noncomputable def repOK (E : Nat → Nat → Nat) (RP : Nat → Nat) (i : Nat) : Bool :=
  strictB (RP i) fun x =>
    bAnd(fixIn (Nat.shiftRight x (nat_lit 10)),
      Nat.beq (cntFix (E (Nat.land x (nat_lit 1023))) (nat_lit 820)) (Nat.shiftRight x (nat_lit 10)))

@[expose] noncomputable def cjAt (E Ei : Nat → Nat → Nat) (k j m q : Nat) : Bool :=
  Nat.beq (E m (E j (Ei m q))) (E k q)

@[expose] noncomputable def cjOK (E Ei : Nat → Nat → Nat) (F RP CJ : Nat → Nat) (nr k : Nat) : Bool :=
  bIf(Nat.blt (Nat.land (F k) (nat_lit 3)) (nat_lit 2), true,
    strictB (CJ k) fun x => strictB (Nat.land x (nat_lit 15)) fun i =>
      strictB (Nat.shiftRight x (nat_lit 4)) fun m => strictB (Nat.land (RP i) (nat_lit 1023)) fun j =>
        bAnd(Nat.blt i nr, bAnd(Nat.blt m (nat_lit 1024),
        bAnd(cjAt E Ei k j m (nat_lit 0), bAnd(cjAt E Ei k j m (nat_lit 1),
        bAnd(cjAt E Ei k j m (nat_lit 9), cjAt E Ei k j m (nat_lit 84)))))))

@[expose] noncomputable def sumMask (SZ nb : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 1)
    (fun i ih => Nat.lor ih (Nat.shiftLeft ih (fld(SZ, Nat.mul (nat_lit 8) i, nat_lit 255)))) nb

@[expose] noncomputable def noFixSum (SZ nb : Nat) : Bool :=
  strictB (sumMask SZ nb) fun M =>
    bAnd(Nat.beq (fld(M, nat_lit 20, nat_lit 1)) (nat_lit 0),
    bAnd(Nat.beq (fld(M, nat_lit 40, nat_lit 1)) (nat_lit 0),
      Nat.beq (fld(M, nat_lit 92, nat_lit 1)) (nat_lit 0)))

@[expose] noncomputable def cntSz (SZ nb s : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i ih => nIf(Nat.beq (fld(SZ, Nat.mul (nat_lit 8) i, nat_lit 255)) s, Nat.succ ih, ih)) nb

end CFSG.KC.U43Alpha
