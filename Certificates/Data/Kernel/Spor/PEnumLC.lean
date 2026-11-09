module

public import Certificates.Data.Kernel.Spor.PEnum

public section

namespace CFSG.KS.PEnumLC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PEnum

@[expose] noncomputable def penumPtLC (n w m : Nat) (conj : Bool) (G GI : Nat → Nat) (k cnt : Nat)
    (T PL POS SRT SRI : Nat → Nat) (i : Nat) : Bool :=
  strictB (T i) (fun t =>
  bAnd(bIf(Nat.beq i (nat_lit 0), true,
    strictB (parOf PL i) (fun p => strictB (labOf PL i) (fun l =>
    bAnd(Nat.blt p i, bAnd(Nat.blt l k, bAnd(Nat.beq (r32 POS (Nat.add (Nat.mul p k) l)) i,
      bIf(Nat.blt (Nat.succ i) cnt,
        lexLtK p l (parOf PL (Nat.succ i)) (labOf PL (Nat.succ i)), true))))))),
  bAnd(allN k (fun j => strictB (r32 POS (Nat.add (Nat.mul i k) j)) (fun q =>
    bAnd(Nat.blt q cnt, bAnd(Nat.beq (T q) (stepK n w m conj G GI j t),
      bIf(Nat.beq q (nat_lit 0), true,
        bIf(lexLtK i j (parOf PL q) (labOf PL q), false, true)))))),
  strictB (r32 SRT i) (fun s => bAnd(Nat.blt s cnt, bAnd(Nat.beq (r32 SRI s) i,
    bIf(Nat.blt (Nat.succ i) cnt, Nat.blt (T s) (T (r32 SRT (Nat.succ i))), true)))))))

@[expose] noncomputable def penumSlLC (n w m : Nat) (conj : Bool) (G GI : Nat → Nat) (k cnt : Nat)
    (T PL POS SRT SRI : Nat → Nat) (lo len : Nat) : Bool :=
  allN len (fun d => strictB (Nat.add lo d) (fun i =>
    bIf(Nat.blt i cnt, penumPtLC n w m conj G GI k cnt T PL POS SRT SRI i, true)))

end CFSG.KS.PEnumLC

end
