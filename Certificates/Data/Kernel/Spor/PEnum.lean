module

public import Certificates.Data.Kernel.Spor.Prim
public import Certificates.Data.Kernel.Spor.Row

public section

namespace CFSG.KS.PEnum

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.Row

@[expose] noncomputable def r32 (F : Nat → Nat) (i : Nat) : Nat :=
  rg (nat_lit 32) (nat_lit 4294967295) F (nat_lit 0) i

@[expose] noncomputable def parOf (PL : Nat → Nat) (i : Nat) : Nat :=
  Nat.shiftRight (r32 PL i) (nat_lit 12)

@[expose] noncomputable def labOf (PL : Nat → Nat) (i : Nat) : Nat :=
  Nat.land (r32 PL i) (nat_lit 4095)

@[expose] noncomputable def stepK (n w m : Nat) (conj : Bool) (G GI : Nat → Nat) (j t : Nat) :
    Nat :=
  nIf(conj, pcomp n w m (pcomp n w m (G j) t) (GI j), pcomp n w m (G j) t)

@[expose] noncomputable def penumHdK (root cnt cap : Nat) (T PL : Nat → Nat) : Bool :=
  bAnd(Nat.blt (nat_lit 0) cnt, bAnd(Nat.ble cnt cap,
    bAnd(Nat.beq (T (nat_lit 0)) root, Nat.beq (r32 PL (nat_lit 0)) (nat_lit 0))))

@[expose] noncomputable def penumPtK (n w m nw : Nat) (conj : Bool) (G GI : Nat → Nat)
    (k cnt : Nat) (T PL POS SRT SRI : Nat → Nat) (i : Nat) : Bool :=
  strictB (T i) (fun t =>
  bAnd(canonK n w m nw t,
  bAnd(bIf(Nat.beq i (nat_lit 0), true,
    strictB (parOf PL i) (fun p => strictB (labOf PL i) (fun l =>
    bAnd(Nat.blt p i, bAnd(Nat.blt l k, bAnd(Nat.beq t (stepK n w m conj G GI l (T p)),
      bIf(Nat.blt (Nat.succ i) cnt,
        lexLtK p l (parOf PL (Nat.succ i)) (labOf PL (Nat.succ i)), true))))))),
  bAnd(allN k (fun j => strictB (r32 POS (Nat.add (Nat.mul i k) j)) (fun q =>
    bAnd(Nat.blt q cnt, bAnd(Nat.beq (T q) (stepK n w m conj G GI j t),
      bIf(Nat.beq q (nat_lit 0), true,
        bIf(lexLtK i j (parOf PL q) (labOf PL q), false, true)))))),
  strictB (r32 SRT i) (fun s => bAnd(Nat.blt s cnt, bAnd(Nat.beq (r32 SRI s) i,
    bIf(Nat.blt (Nat.succ i) cnt, Nat.blt (T s) (T (r32 SRT (Nat.succ i))), true))))))))

@[expose] noncomputable def penumSlK (n w m nw : Nat) (conj : Bool) (G GI : Nat → Nat)
    (k cnt : Nat) (T PL POS SRT SRI : Nat → Nat) (lo len : Nat) : Bool :=
  allN len (fun d => strictB (Nat.add lo d) (fun i =>
    bIf(Nat.blt i cnt, penumPtK n w m nw conj G GI k cnt T PL POS SRT SRI i, true)))

end CFSG.KS.PEnum

end
