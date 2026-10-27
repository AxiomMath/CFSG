module

public import Certificates.Data.Kernel.Spor.PEnum

public section

namespace CFSG.KS.PEnumC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum

@[expose] noncomputable def penumPtC (k K cnt : Nat) (T PL POS CL SRT SRI : Nat → Nat) (i : Nat) :
    Bool :=
  bAnd(bIf(Nat.beq i (nat_lit 0), true,
    strictB (parOf PL i) (fun p => strictB (labOf PL i) (fun l =>
    bAnd(Nat.blt p i, bAnd(Nat.blt l k, bAnd(Nat.beq (r32 CL (Nat.add (Nat.mul p K) l)) i,
      bIf(Nat.blt (Nat.succ i) cnt,
        lexLtK p l (parOf PL (Nat.succ i)) (labOf PL (Nat.succ i)), true))))))),
  bAnd(allN k (fun j => strictB (r32 POS (Nat.add (Nat.mul i k) j)) (fun q =>
    bAnd(Nat.blt q cnt, bAnd(Nat.beq q (r32 CL (Nat.add (Nat.mul i K) j)),
      bIf(Nat.beq q (nat_lit 0), true,
        bIf(lexLtK i j (parOf PL q) (labOf PL q), false, true)))))),
  strictB (r32 SRT i) (fun s => bAnd(Nat.blt s cnt, bAnd(Nat.beq (r32 SRI s) i,
    bIf(Nat.blt (Nat.succ i) cnt, Nat.blt (T s) (T (r32 SRT (Nat.succ i))), true))))))

@[expose] noncomputable def penumSlC (k K cnt : Nat) (T PL POS CL SRT SRI : Nat → Nat)
    (lo len : Nat) : Bool :=
  allN len (fun d => strictB (Nat.add lo d) (fun i =>
    bIf(Nat.blt i cnt, penumPtC k K cnt T PL POS CL SRT SRI i, true)))

end CFSG.KS.PEnumC

end
