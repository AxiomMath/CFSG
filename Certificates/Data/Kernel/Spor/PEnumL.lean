module

public import Certificates.Data.Kernel.Spor.PEnum

public section

namespace CFSG.KS.PEnumL

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PEnum

@[expose] noncomputable def penumPtL (n w m : Nat) (G : Nat → Nat) (k cnt : Nat)
    (T PL POS SRT SRI : Nat → Nat) (i : Nat) : Bool :=
  strictB (T i) (fun t =>
  bAnd(bIf(Nat.beq i (nat_lit 0), true,
    strictB (parOf PL i) (fun p => strictB (labOf PL i) (fun l =>
    bAnd(Nat.blt p i, bAnd(Nat.blt l k, bAnd(Nat.beq (r32 POS (Nat.add (Nat.mul p k) l)) i,
      bIf(Nat.blt (Nat.succ i) cnt,
        lexLtK p l (parOf PL (Nat.succ i)) (labOf PL (Nat.succ i)), true))))))),
  bAnd(allN k (fun j => strictB (r32 POS (Nat.add (Nat.mul i k) j)) (fun q =>
    bAnd(Nat.blt q cnt, bAnd(Nat.beq (T q) (pcomp n w m (G j) t),
      bIf(Nat.beq q (nat_lit 0), true,
        bIf(lexLtK i j (parOf PL q) (labOf PL q), false, true)))))),
  strictB (r32 SRT i) (fun s => bAnd(Nat.blt s cnt, bAnd(Nat.beq (r32 SRI s) i,
    bIf(Nat.blt (Nat.succ i) cnt, Nat.blt (T s) (T (r32 SRT (Nat.succ i))), true)))))))

@[expose] noncomputable def penumSlL (n w m : Nat) (G : Nat → Nat) (k cnt : Nat)
    (T PL POS SRT SRI : Nat → Nat) (lo len : Nat) : Bool :=
  allN len (fun d => strictB (Nat.add lo d) (fun i =>
    bIf(Nat.blt i cnt, penumPtL n w m G k cnt T PL POS SRT SRI i, true)))

end CFSG.KS.PEnumL

end
