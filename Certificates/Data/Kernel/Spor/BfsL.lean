module

public import Certificates.Data.Kernel.Spor.PEnum

public section

namespace CFSG.KS.BfsL

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PEnum

@[expose] noncomputable def noneK : Nat := nat_lit 4294967295

@[expose] noncomputable def bfsLHdK (m root cnt : Nat) (PTS POS PAR LAB : Nat → Nat) : Bool :=
  bAnd(Nat.blt (nat_lit 0) cnt, bAnd(Nat.ble cnt m, bAnd(Nat.blt m noneK, bAnd(Nat.blt root m,
  bAnd(Nat.beq (r32 PTS (nat_lit 0)) root, bAnd(Nat.beq (r32 PAR (nat_lit 0)) (nat_lit 0),
  bAnd(Nat.beq (r32 LAB (nat_lit 0)) (nat_lit 0),
    allN m (fun z => strictB (r32 POS z) (fun q =>
      bIf(Nat.beq q noneK, true, bAnd(Nat.blt q cnt, Nat.beq (r32 PTS q) z)))))))))))

@[expose] noncomputable def bfsLPtK (m cnt k : Nat) (L : Nat → Nat → Nat)
    (PTS POS PAR LAB : Nat → Nat) (i : Nat) : Bool :=
  strictB (r32 PTS i) (fun p =>
  bAnd(Nat.blt p m, bAnd(Nat.beq (r32 POS p) i,
  bAnd(bIf(Nat.beq i (nat_lit 0), true,
    strictB (r32 PAR i) (fun pa => strictB (r32 LAB i) (fun s =>
    bAnd(Nat.blt pa i, bAnd(Nat.blt s k, bAnd(Nat.beq (L s (r32 PTS pa)) p,
      bIf(Nat.blt (Nat.succ i) cnt,
        lexLtK pa s (r32 PAR (Nat.succ i)) (r32 LAB (Nat.succ i)), true))))))),
  allN k (fun s => strictB (L s p) (fun q => bIf(Nat.blt q m,
    strictB (r32 POS q) (fun iq => bAnd(Nat.blt iq cnt, bIf(Nat.beq iq (nat_lit 0), true,
      bIf(lexLtK i s (r32 PAR iq) (r32 LAB iq), false, true)))), true)))))))

@[expose] noncomputable def bfsLSlK (m cnt k : Nat) (L : Nat → Nat → Nat)
    (PTS POS PAR LAB : Nat → Nat) (lo len : Nat) : Bool :=
  allN len (fun d => strictB (Nat.add lo d) (fun i =>
    bIf(Nat.blt i cnt, bfsLPtK m cnt k L PTS POS PAR LAB i, true)))

end CFSG.KS.BfsL

end
