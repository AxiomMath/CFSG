module

public import Certificates.Data.Kernel.Spor.PEnum

public section

namespace CFSG.KS.TBfs

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PEnum

@[expose] noncomputable def none32K : Nat := nat_lit 4294967295

@[expose] noncomputable def tbfsHdK (n root cnt : Nat) (PTS POS PAR LAB : Nat → Nat) : Bool :=
  bAnd(Nat.blt (nat_lit 0) cnt, bAnd(Nat.ble cnt n, bAnd(Nat.blt n none32K,
  bAnd(Nat.beq (r32 PTS (nat_lit 0)) root, bAnd(Nat.beq (r32 PAR (nat_lit 0)) (nat_lit 0),
  bAnd(Nat.beq (r32 LAB (nat_lit 0)) (nat_lit 0),
    allN n (fun z => strictB (r32 POS z) (fun q =>
      bIf(Nat.beq q none32K, true, bAnd(Nat.blt q cnt, Nat.beq (r32 PTS q) z))))))))))

@[expose] noncomputable def tbfsPtK (n cnt r : Nat) (L : Nat → Nat → Nat) (LV : Nat → Nat)
    (PTS POS PAR LAB TI : Nat → Nat) (k : Nat) : Bool :=
  strictB (r32 PTS k) (fun p =>
  bAnd(Nat.blt p n, bAnd(Nat.beq (r32 POS p) k,
  bAnd(bIf(Nat.beq k (nat_lit 0), true,
    strictB (r32 PAR k) (fun pa => strictB (r32 TI k) (fun t =>
    bAnd(Nat.blt pa k, bAnd(Nat.blt t r, bAnd(Nat.beq (r32 LAB k) (LV t),
    bAnd(Nat.beq (L (LV t) (r32 PTS pa)) p,
      bIf(Nat.blt (Nat.succ k) cnt,
        lexLtK pa t (r32 PAR (Nat.succ k)) (r32 TI (Nat.succ k)), true)))))))),
  allN r (fun t => strictB (L (LV t) p) (fun q => bAnd(Nat.blt q n, strictB (r32 POS q) (fun kq =>
    bAnd(Nat.blt kq cnt, bIf(Nat.beq kq (nat_lit 0), true,
      bIf(lexLtK k t (r32 PAR kq) (r32 TI kq), false, true)))))))))))

@[expose] noncomputable def tbfsSlK (n cnt r : Nat) (L : Nat → Nat → Nat) (LV : Nat → Nat)
    (PTS POS PAR LAB TI : Nat → Nat) (lo len : Nat) : Bool :=
  allN len (fun d => strictB (Nat.add lo d) (fun k =>
    bIf(Nat.blt k cnt, tbfsPtK n cnt r L LV PTS POS PAR LAB TI k, true)))

end CFSG.KS.TBfs

end
