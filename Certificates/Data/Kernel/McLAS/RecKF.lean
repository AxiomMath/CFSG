module

public import Certificates.Data.Kernel.McLAS.Pair
public import Certificates.Data.Kernel.McLAS.Slices
public import Certificates.Data.Kernel.Spor.MulHF

public section

namespace CFSG.KS.McLAS

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH

@[expose] noncomputable def pairSelKF (a x : Nat) : Bool :=
  bAnd(Nat.beq (fixK x) (nat_lit 5), bAnd(Nat.beq (pwK (nat_lit 3) x) idK,
    bAnd(bIf(Nat.beq (pwK (nat_lit 1) x) idK, false, true), bAnd(bIf(Nat.beq x idK, false, true),
      bAnd(bIf(Nat.beq x a, false, true), bIf(Nat.beq x (pcK a a), false, true))))))

@[expose] noncomputable def penumPtKF (n w m nw : Nat) (GI : Nat → Nat) (k cnt : Nat)
    (T PL POS SRT SRI : Nat → Nat) (i : Nat) : Bool :=
  strictB (T i) (fun t =>
  bAnd(canonK n w m nw t,
  bAnd(bIf(Nat.beq i (nat_lit 0), true,
    strictB (parOf PL i) (fun p => strictB (labOf PL i) (fun l =>
    bAnd(Nat.blt p i, bAnd(Nat.blt l k, bAnd(Nat.beq (r32 POS (Nat.add (Nat.mul p k) l)) i,
      bIf(Nat.blt (Nat.succ i) cnt,
        lexLtK p l (parOf PL (Nat.succ i)) (labOf PL (Nat.succ i)), true))))))),
  bAnd(allN k (fun j => strictB (r32 POS (Nat.add (Nat.mul i k) j)) (fun q =>
    bAnd(Nat.blt q cnt, bAnd(Nat.beq (T q) (pcomp n w m t (GI j)),
      bIf(Nat.beq q (nat_lit 0), true,
        bIf(lexLtK i j (parOf PL q) (labOf PL q), false, true)))))),
  strictB (r32 SRT i) (fun s => bAnd(Nat.blt s cnt, bAnd(Nat.beq (r32 SRI s) i,
    bIf(Nat.blt (Nat.succ i) cnt, Nat.blt (T s) (T (r32 SRT (Nat.succ i))), true))))))))

@[expose] noncomputable def recSlRF (GI : Nat → Nat) (k cnt : Nat)
    (T PL POS SRT SRI HS HSI : Nat → Nat) (lo len : Nat) : Bool :=
  bAnd(slK cnt (penumPtKF (nat_lit 275) (nat_lit 9) (mask (nat_lit 9)) (nat_lit 2475) GI k cnt T PL
      POS SRT SRI) lo len,
    slK cnt (hsortPtKF (nat_lit 275) (nat_lit 9) (mask (nat_lit 9)) cnt T HS HSI) lo len)

end CFSG.KS.McLAS

end
