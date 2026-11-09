module

public import Certificates.Data.Kernel.SporSch.J4SSylow

public section

namespace CFSG.KS.H13J4

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.C11

@[expose] noncomputable def conjK (P Q B : Nat) : Nat := compK (compK P B) Q

@[expose] noncomputable def appTabK (L a : Nat) : Nat :=
  fld(L, Nat.mul (nat_lit 11) a, nat_lit 2047)

@[expose] noncomputable def compTabK (L B : Nat) : Nat := packK (fun j => appTabK L (colK B j))

@[expose] noncomputable def appTabOK (P L : Nat) : Bool :=
  allN (nat_lit 2048) fun a => Nat.beq (appTabK L a) (appK P a)

@[expose] noncomputable def rowK (R k : Nat) : Nat :=
  fld(R, Nat.mul (nat_lit 121) k, nat_lit 2658455991569831745807614120560689151)

@[expose] noncomputable def rowOK (P R : Nat) : Bool :=
  allN (nat_lit 11) fun k =>
    Nat.beq (rowK R k) (packK fun j => Nat.land (Nat.shiftRight (colK P j) k) (nat_lit 1))

@[expose] noncomputable def conjTabK (L R B : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => strictN acc fun s =>
      Nat.xor s (Nat.mul (appTabK L (colK B k)) (rowK R k))) (nat_lit 11)

@[expose] noncomputable def stepK (L R T GEN NX : Nat → Nat) (m n i : Nat) : Bool :=
  strictB (T i) fun t =>
    bAnd(bIf(Nat.beq i (nat_lit 0), true, strictB (GEN i) fun g =>
        bAnd(Nat.blt g m, Nat.blt (NX (Nat.add (Nat.mul m i) g)) i)),
      allN m fun g => strictB (NX (Nat.add (Nat.mul m i) g)) fun j =>
        bAnd(Nat.blt j n, Nat.beq (T j) (conjTabK (L g) (R g) t)))

@[expose] noncomputable def stepAt (L R T GEN NX : Nat → Nat) (m n i : Nat) : Bool :=
  bIf(Nat.blt i n, stepK L R T GEN NX m n i, true)

end CFSG.KS.H13J4

end
