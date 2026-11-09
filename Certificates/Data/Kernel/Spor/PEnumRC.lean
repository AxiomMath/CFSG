module

public import Certificates.Data.Kernel.Spor.PEnumR

public section

namespace CFSG.KS.PEnumRC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PEnum CFSG.KS.MulH

@[expose] noncomputable def penumPtRC (n w m : Nat) (G GI : Nat → Nat) (k cnt : Nat)
    (T PL POS SRT SRI : Nat → Nat) (i : Nat) : Bool :=
  strictB (T i) (fun t =>
  bAnd(bIf(Nat.beq i (nat_lit 0), true,
    strictB (parOf PL i) (fun p => strictB (labOf PL i) (fun l =>
    bAnd(Nat.blt p i, bAnd(Nat.blt l k, bAnd(Nat.beq (r32 POS (Nat.add (Nat.mul p k) l)) i,
      bIf(Nat.blt (Nat.succ i) cnt,
        lexLtK p l (parOf PL (Nat.succ i)) (labOf PL (Nat.succ i)), true))))))),
  bAnd(allN k (fun j => strictB (r32 POS (Nat.add (Nat.mul i k) j)) (fun q =>
    bAnd(Nat.blt q cnt, bAnd(Nat.beq (T q) (stepK n w m true G GI j t),
      bIf(Nat.beq q (nat_lit 0), true,
        bIf(lexLtK i j (parOf PL q) (labOf PL q), false, true)))))),
  strictB (r32 SRT i) (fun s => bAnd(Nat.blt s cnt, bAnd(Nat.beq (r32 SRI s) i,
    bIf(Nat.blt (Nat.succ i) cnt, Nat.blt (T s) (T (r32 SRT (Nat.succ i))), true)))))))

@[expose] noncomputable def recPtK (n w m : Nat) (G GI : Nat → Nat) (k : Nat) (T PL : Nat → Nat)
    (i : Nat) : Bool :=
  bIf(Nat.beq i (nat_lit 0), true,
    strictB (parOf PL i) (fun p => strictB (labOf PL i) (fun l =>
    bAnd(Nat.blt p i, bAnd(Nat.blt l k, Nat.beq (T i) (stepK n w m true G GI l (T p)))))))

@[expose] noncomputable def recMulPtK (n w m : Nat) (GI : Nat → Nat) (k : Nat) (T PL : Nat → Nat)
    (i : Nat) : Bool :=
  bIf(Nat.beq i (nat_lit 0), true,
    strictB (parOf PL i) (fun p => strictB (labOf PL i) (fun l =>
    bAnd(Nat.blt p i, bAnd(Nat.blt l k, Nat.beq (T i) (pcomp n w m (T p) (GI l)))))))

@[expose] noncomputable def recParArr (cnt : Nat) (PL : Nat → Nat) : Array (Nat × Nat) :=
  Array.ofFn (n := cnt - 1) fun i => (parOf PL (i.val + 1), labOf PL (i.val + 1))

end CFSG.KS.PEnumRC

end
