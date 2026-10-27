module

public import Certificates.Data.Kernel.LceSTab

public section

namespace CFSG.KC.LceJson

open CFSG.KC CFSG.KC.LceS

@[expose] noncomputable def sel2 (R : List (List Nat)) (k : Nat) : Nat :=
  List.getD (List.getD R (Nat.shiftRight k (nat_lit 5)) []) (Nat.land k (nat_lit 31)) (nat_lit 0)

@[expose] noncomputable def sel1 (R : List Nat) (k : Nat) : Nat := List.getD R k (nat_lit 0)

@[expose] noncomputable def selW (WT : List (List Nat)) (m k : Nat) : Nat := sel2 WT (Nat.mod k m)

@[expose] noncomputable def tabOk (B WT : List (List Nat)) (RT ST LV : List Nat)
    (INV INV8 L nC mLV a m Hs nR nS nf : Nat) (JF JV : List Nat) (S1 X1 : Nat) : Bool :=
  CFSG.Certificates.LCE.lceOk (sel2 B) (selW WT m) (sel1 RT) (sel1 ST) (sel1 LV) INV INV8 L nC nC mLV a m
    Hs nR nS nf JF JV (mkS (nat_lit 0) (nat_lit 1)) S1 (nat_lit 1) X1

end CFSG.KC.LceJson

end
