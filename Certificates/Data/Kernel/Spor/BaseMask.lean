module

public import Certificates.Data.Kernel.Spor.PEnum

public section

namespace CFSG.KS.BaseMask

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PEnum

@[expose] noncomputable def bkeyK (n w m b c X : Nat) : Nat :=
  Nat.add (Nat.mul (pg w m X b) n) (pg w m X c)

@[expose] noncomputable def bsortPtK (n w m b c cnt : Nat) (T KS KSI : Nat → Nat) (i : Nat) :
    Bool :=
  strictB (r32 KS i) (fun s => bAnd(Nat.blt s cnt, bAnd(Nat.beq (r32 KSI s) i,
    bIf(Nat.blt (Nat.succ i) cnt,
      Nat.blt (bkeyK n w m b c (T s)) (bkeyK n w m b c (T (r32 KS (Nat.succ i)))), true))))

@[expose] noncomputable def mulKeyK (w m b c : Nat) (T : Nat → Nat) (i j q : Nat) : Bool :=
  bAnd(Nat.beq (pg w m (T i) (pg w m (T j) b)) (pg w m (T q) b),
    Nat.beq (pg w m (T i) (pg w m (T j) c)) (pg w m (T q) c))

@[expose] noncomputable def commKeyK (w m b c : Nat) (T : Nat → Nat) (s g : Nat) : Bool :=
  bAnd(Nat.beq (pg w m (T s) (pg w m (T g) b)) (pg w m (T g) (pg w m (T s) b)),
    Nat.beq (pg w m (T s) (pg w m (T g) c)) (pg w m (T g) (pg w m (T s) c)))

@[expose] noncomputable def conjKeyK (w m b c : Nat) (T : Nat → Nat) (y a d : Nat) : Bool :=
  bAnd(Nat.beq (pg w m (T y) (pg w m (T a) b)) (pg w m (T d) (pg w m (T y) b)),
    Nat.beq (pg w m (T y) (pg w m (T a) c)) (pg w m (T d) (pg w m (T y) c)))

@[expose] noncomputable def maskK (I : Nat → Nat) (o len : Nat) : Nat :=
  foldN len (fun e M => Nat.lor M (Nat.shiftLeft (nat_lit 1) (r32 I (Nat.add o e)))) (nat_lit 0)

@[expose] noncomputable def distinctK (cnt : Nat) (I : Nat → Nat) (o len : Nat) : Bool :=
  Nat.blt (foldN len (fun e M => strictN (r32 I (Nat.add o e)) (fun q =>
      nIf(hasBit M q, Nat.lor M (Nat.shiftLeft (nat_lit 1) cnt),
        Nat.lor M (Nat.shiftLeft (nat_lit 1) q)))) (nat_lit 0))
    (Nat.shiftLeft (nat_lit 1) cnt)

@[expose] noncomputable def involMaskK (w m b c cnt : Nat) (T IV : Nat → Nat) (niv : Nat) : Bool :=
  strictB (maskK IV (nat_lit 0) niv) (fun M => bAnd(Nat.blt M (Nat.shiftLeft (nat_lit 1) cnt),
    allN cnt (fun i => bIf(hasBit M i,
      bAnd(bIf(Nat.beq i (nat_lit 0), false, true), mulKeyK w m b c T i i (nat_lit 0)),
      bIf(Nat.beq i (nat_lit 0), true, bIf(mulKeyK w m b c T i i (nat_lit 0), false, true))))))

@[expose] noncomputable def cmaskK (w m b c : Nat) (T IV : Nat → Nat) (niv IM C g : Nat) : Bool :=
  bAnd(Nat.beq (Nat.land C IM) C,
    allN niv (fun t => strictB (r32 IV t) (fun s =>
      bIf(hasBit C s, commKeyK w m b c T s g, bIf(commKeyK w m b c T s g, false, true)))))

@[expose] noncomputable def memberK (w m b c cnt : Nat) (T I : Nat → Nat) (o k : Nat) : Bool :=
  bAnd(Nat.beq (r32 I o) (nat_lit 0), bAnd(distinctK cnt I o (Nat.shiftLeft (nat_lit 1) k),
    allN (Nat.shiftLeft (nat_lit 1) k) (fun e => strictB (r32 I (Nat.add o e)) (fun x =>
      allN k (fun j => mulKeyK w m b c T x (r32 I (Nat.add o (Nat.shiftLeft (nat_lit 1) j)))
        (r32 I (Nat.add o (Nat.xor e (Nat.shiftLeft (nat_lit 1) j)))))))))

@[expose] noncomputable def coverK (I : Nat → Nat) (on nc k' M : Nat) : Nat :=
  foldN nc (fun h U => strictN (maskK I (Nat.add on (Nat.mul h (Nat.shiftLeft (nat_lit 1) k')))
      (Nat.shiftLeft (nat_lit 1) k')) (fun X =>
    nIf(Nat.beq (Nat.land M X) M, Nat.lor U X, U))) (nat_lit 0)

@[expose] noncomputable def extK (I GS CM : Nat → Nat) (IM o go k on nc : Nat) : Bool :=
  strictB (maskK I o (Nat.shiftLeft (nat_lit 1) k)) (fun M =>
  strictB (foldN k (fun j C => Nat.land C (CM (r32 GS (Nat.add go j)))) (Nat.xor IM (Nat.land IM M)))
    (fun C => strictB (coverK I on nc (Nat.succ k) M) (fun U => Nat.beq (Nat.land C U) C)))

@[expose] noncomputable def conjMemK (w m b c : Nat) (T A D : Nat → Nat) (y len : Nat) : Bool :=
  allN len (fun e => conjKeyK w m b c T y (r32 A e) (r32 D e))

end CFSG.KS.BaseMask

end
