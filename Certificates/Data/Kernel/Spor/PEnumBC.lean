module

public import Certificates.Data.Kernel.Spor.PEnumB

public section

namespace CFSG.KS.PEnumB

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum

@[expose] noncomputable def penumPtBC (n w m : Nat) (bs : List Nat) (G GI : Nat → Nat)
    (k cnt : Nat) (T PL POS SRT SRI : Nat → Nat) (i : Nat) : Bool :=
  strictB (T i) (fun t =>
  bAnd(bIf(Nat.beq i (nat_lit 0), true,
    strictB (parOf PL i) (fun p => strictB (labOf PL i) (fun l =>
    bAnd(Nat.blt p i, bAnd(Nat.blt l k, bAnd(Nat.beq t (stepK n w m true G GI l (T p)),
      bIf(Nat.blt (Nat.succ i) cnt,
        lexLtK p l (parOf PL (Nat.succ i)) (labOf PL (Nat.succ i)), true))))))),
  bAnd(allN k (fun j => strictB (r32 POS (Nat.add (Nat.mul i k) j)) (fun q =>
    bAnd(Nat.blt q cnt, bAnd(agreeC3 w m bs (T q) (G j) t (GI j),
      bIf(Nat.beq q (nat_lit 0), true,
        bIf(lexLtK i j (parOf PL q) (labOf PL q), false, true)))))),
  strictB (r32 SRT i) (fun s => bAnd(Nat.blt s cnt, bAnd(Nat.beq (r32 SRI s) i,
    bIf(Nat.blt (Nat.succ i) cnt, Nat.blt (T s) (T (r32 SRT (Nat.succ i))), true)))))))

@[expose] noncomputable def bkeyLK (w m : Nat) (bs : List Nat) (X : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun b _ ih => Nat.add (Nat.shiftLeft ih (nat_lit 12)) (pg w m X b)) bs

@[expose] noncomputable def bsortLK (w m : Nat) (bs : List Nat) (cnt : Nat) (T HS HSI : Nat → Nat)
    (i : Nat) : Bool :=
  strictB (HS i) (fun s => bAnd(Nat.blt s cnt, bAnd(Nat.beq (HSI s) i,
    bIf(Nat.blt (Nat.succ i) cnt,
      Nat.blt (bkeyLK w m bs (T s)) (bkeyLK w m bs (T (HS (Nat.succ i)))), true))))

@[expose] noncomputable def penumSlBC (n w m : Nat) (bs : List Nat) (G GI : Nat → Nat)
    (k cnt : Nat) (T PL POS SRT SRI : Nat → Nat) (lo len : Nat) : Bool :=
  allN len (fun d => strictB (Nat.add lo d) (fun i =>
    bIf(Nat.blt i cnt, penumPtBC n w m bs G GI k cnt T PL POS SRT SRI i, true)))

end CFSG.KS.PEnumB

end
