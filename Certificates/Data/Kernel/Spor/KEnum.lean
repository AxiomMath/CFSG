module

public import Certificates.Data.Kernel.Spor.FpBfs

public section

namespace CFSG.KS.KEnum

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.FpBfs

@[expose] noncomputable def kenumHdK (n w m nw k kk cnt R : Nat) (G T : Nat → Nat) : Bool :=
  bAnd(Nat.blt (nat_lit 0) k, bAnd(Nat.ble k kk, bAnd(Nat.blt (nat_lit 0) cnt,
  bAnd(Nat.beq (T (nat_lit 0)) R, allN kk (fun s => canonK n w m nw (G s))))))

@[expose] noncomputable def kenumPtK (n w m nw k kk cnt : Nat)
    (G T TI PL POS FP SRT SRI : Nat → Nat) (i : Nat) : Bool :=
  strictB (T i) (fun t =>
  bAnd(canonK n w m nw t, bAnd(permOK n w m nw t (TI i), bAnd(Nat.beq (FP i) (fpK w m t),
  bAnd(bIf(Nat.beq i (nat_lit 0), true, strictB (PL i) (fun c =>
    bAnd(Nat.blt (Nat.div c k) i,
    bAnd(Nat.beq (POS (Nat.add (Nat.mul kk (Nat.div c k)) (Nat.mod c k))) i,
      bIf(Nat.blt (Nat.succ i) cnt, Nat.blt c (PL (Nat.succ i)), true))))),
  bAnd(allN kk (fun s => strictB (POS (Nat.add (Nat.mul kk i) s)) (fun q =>
    bAnd(Nat.blt q cnt, bAnd(Nat.beq (T q) (pcomp n w m (G s) t),
      bIf(Nat.blt s k, bIf(Nat.beq q (nat_lit 0), true,
        Nat.ble (PL q) (Nat.add (Nat.mul k i) s)), true))))),
  bAnd(strictB (SRI i) (fun r => bAnd(Nat.blt r cnt, Nat.beq (SRT r) i)),
  strictB (SRT i) (fun r => bAnd(Nat.blt r cnt, bAnd(Nat.beq (SRI r) i,
    bIf(Nat.blt (Nat.succ i) cnt, Nat.blt (FP r) (FP (SRT (Nat.succ i))), true)))))))))))

@[expose] noncomputable def kenumSlK (n w m nw k kk cnt : Nat)
    (G T TI PL POS FP SRT SRI : Nat → Nat) (lo len : Nat) : Bool :=
  allN len (fun d => strictB (Nat.add lo d) (fun i =>
    bIf(Nat.blt i cnt, kenumPtK n w m nw k kk cnt G T TI PL POS FP SRT SRI i, true)))

end CFSG.KS.KEnum

end
