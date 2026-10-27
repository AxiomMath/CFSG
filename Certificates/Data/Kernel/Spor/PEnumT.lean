module

public import Certificates.Data.Kernel.Spor.PEnum

public section

namespace CFSG.KS.PEnum

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.Row

@[expose] noncomputable def penumHdTK (root cnt : Nat) (T PL : Nat → Nat) : Bool :=
  bAnd(Nat.blt (nat_lit 0) cnt,
    bAnd(Nat.beq (T (nat_lit 0)) root, Nat.beq (r32 PL (nat_lit 0)) (nat_lit 0)))

@[expose] noncomputable def penumPtTK (n w m nw : Nat) (conj : Bool) (G GI : Nat → Nat)
    (k cnt cap : Nat) (T PL POS SRT SRI : Nat → Nat) (i : Nat) : Bool :=
  strictB (T i) (fun t =>
  bAnd(canonK n w m nw t,
  bAnd(bIf(Nat.beq i (nat_lit 0), true,
    strictB (parOf PL i) (fun p => strictB (labOf PL i) (fun l =>
    bAnd(Nat.blt p i, bAnd(Nat.blt p cap, bAnd(Nat.blt l k,
      bAnd(Nat.beq t (stepK n w m conj G GI l (T p)),
      bIf(Nat.blt (Nat.succ i) cnt,
        lexLtK p l (parOf PL (Nat.succ i)) (labOf PL (Nat.succ i)), true)))))))),
  bAnd(bIf(Nat.blt i cap, allN k (fun j => strictB (r32 POS (Nat.add (Nat.mul i k) j)) (fun q =>
    bAnd(Nat.blt q cnt, bAnd(Nat.beq (T q) (stepK n w m conj G GI j t),
      bIf(Nat.beq q (nat_lit 0), true,
        bIf(lexLtK i j (parOf PL q) (labOf PL q), false, true)))))), true),
  strictB (r32 SRT i) (fun s => bAnd(Nat.blt s cnt, bAnd(Nat.beq (r32 SRI s) i,
    bIf(Nat.blt (Nat.succ i) cnt, Nat.blt (T s) (T (r32 SRT (Nat.succ i))), true))))))))

end CFSG.KS.PEnum

end
