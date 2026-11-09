module

public import Certificates.Data.Kernel.Spor.PEnum

public section

namespace CFSG.KS.TBfs

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PEnum

@[expose] noncomputable def tpathHdK (root cnt : Nat) (PTS : Nat → Nat) : Bool :=
  bAnd(Nat.blt (nat_lit 0) cnt, Nat.beq (r32 PTS (nat_lit 0)) root)

@[expose] noncomputable def tpathPtK (n r : Nat) (L : Nat → Nat → Nat) (LV : Nat → Nat)
    (PTS POS PAR LAB TI : Nat → Nat) (k : Nat) : Bool :=
  strictB (r32 PTS k) (fun p =>
  bAnd(Nat.blt p n, bAnd(Nat.beq (r32 POS p) k,
  bIf(Nat.beq k (nat_lit 0), true,
    strictB (r32 PAR k) (fun pa => strictB (r32 TI k) (fun t =>
    bAnd(Nat.blt pa k, bAnd(Nat.blt t r, bAnd(Nat.beq (r32 LAB k) (LV t),
      Nat.beq (L (LV t) (r32 PTS pa)) p)))))))))

@[expose] noncomputable def tpathSlK (n cnt r : Nat) (L : Nat → Nat → Nat) (LV : Nat → Nat)
    (PTS POS PAR LAB TI : Nat → Nat) (lo len : Nat) : Bool :=
  allN len (fun d => strictB (Nat.add lo d) (fun k =>
    bIf(Nat.blt k cnt, tpathPtK n r L LV PTS POS PAR LAB TI k, true)))

end CFSG.KS.TBfs

end
