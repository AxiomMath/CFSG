module

public import Certificates.Data.Kernel.Spor.PEnum
public import Certificates.Data.Kernel.Spor.MulH

public section

namespace CFSG.KS.PEnumB

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH

@[expose] noncomputable def agreeC (w m : Nat) (bs : List Nat) (X P Q : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun b _ ih => bAnd(Nat.beq (pg w m X b) (pg w m P (pg w m Q b)), ih)) bs

@[expose] noncomputable def agreeC3 (w m : Nat) (bs : List Nat) (X A B C : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun b _ ih => bAnd(Nat.beq (pg w m X b) (pg w m A (pg w m B (pg w m C b))), ih)) bs

@[expose] noncomputable def penumPtB (n w m : Nat) (bs : List Nat) (GI : Nat → Nat)
    (k cnt : Nat) (T PL POS SRT SRI : Nat → Nat) (i : Nat) : Bool :=
  strictB (T i) (fun t =>
  bAnd(bIf(Nat.beq i (nat_lit 0), true,
    strictB (parOf PL i) (fun p => strictB (labOf PL i) (fun l =>
    bAnd(Nat.blt p i, bAnd(Nat.blt l k, bAnd(Nat.beq t (pcomp n w m (T p) (GI l)),
      bIf(Nat.blt (Nat.succ i) cnt,
        lexLtK p l (parOf PL (Nat.succ i)) (labOf PL (Nat.succ i)), true))))))),
  bAnd(allN k (fun j => strictB (r32 POS (Nat.add (Nat.mul i k) j)) (fun q =>
    bAnd(Nat.blt q cnt, bAnd(agreeC w m bs (T q) t (GI j),
      bIf(Nat.beq q (nat_lit 0), true,
        bIf(lexLtK i j (parOf PL q) (labOf PL q), false, true)))))),
  strictB (r32 SRT i) (fun s => bAnd(Nat.blt s cnt, bAnd(Nat.beq (r32 SRI s) i,
    bIf(Nat.blt (Nat.succ i) cnt, Nat.blt (T s) (T (r32 SRT (Nat.succ i))), true)))))))

@[expose] noncomputable def hvK (n w m : Nat) (T HV : Nat → Nat) (i : Nat) : Bool :=
  Nat.beq (hkeyK n w m (T i)) (HV i)

@[expose] noncomputable def hsortVK (cnt : Nat) (HV HS HSI : Nat → Nat) (i : Nat) : Bool :=
  strictB (r32 HS i) (fun s => bAnd(Nat.blt s cnt, bAnd(Nat.beq (r32 HSI s) i,
    bIf(Nat.blt (Nat.succ i) cnt, Nat.blt (HV s) (HV (r32 HS (Nat.succ i))), true))))

@[expose] noncomputable def findProdB (cnt w m : Nat) (bs : List Nat) (K : Nat) (T S POS : Nat → Nat)
    (c : Nat) : Bool :=
  strictB (r32 POS c) (fun q => bAnd(Nat.blt q cnt,
    agreeC w m bs (T q) (T (Nat.div c K)) (S (Nat.mod c K))))

@[expose] noncomputable def findConjB (cnt w m : Nat) (bs : List Nat) (K : Nat)
    (T C CI POS : Nat → Nat) (c : Nat) : Bool :=
  strictB (r32 POS c) (fun q => bAnd(Nat.blt q cnt,
    agreeC3 w m bs (T q) (C (Nat.mod c K)) (T (Nat.div c K)) (CI (Nat.mod c K))))

@[expose] noncomputable def commB (w m : Nat) (bs : List Nat) (X Y : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun b _ ih => bAnd(Nat.beq (pg w m X (pg w m Y b)) (pg w m Y (pg w m X b)), ih)) bs

@[expose] noncomputable def sqB (w m : Nat) (bs : List Nat) (X : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun b _ ih => bAnd(Nat.beq (pg w m X (pg w m X b)) b, ih)) bs

@[expose] noncomputable def spanAtL (w m : Nat) (L : List Nat) : Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ y => y)
    (fun b _ ih mask y => nIf(Nat.beq (Nat.mod mask (nat_lit 2)) (nat_lit 1),
      pg w m b (ih (Nat.div mask (nat_lit 2)) y), ih (Nat.div mask (nat_lit 2)) y)) L

@[expose] noncomputable def spanCompB (w m : Nat) (bs L : List Nat) (X B Y mask : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun b _ ih => bAnd(Nat.beq (pg w m X (pg w m B b)) (spanAtL w m L mask (pg w m Y b)), ih)) bs

@[expose] noncomputable def spanEqB (w m : Nat) (bs L : List Nat) (X mask : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun b _ ih => bAnd(Nat.beq (pg w m X b) (spanAtL w m L mask b), ih)) bs

@[expose] noncomputable def conjSpanB (w m : Nat) (bs L : List Nat) (S X mask : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun b _ ih => bAnd(Nat.beq (pg w m S (spanAtL w m L mask b)) (pg w m X (pg w m S b)), ih)) bs

@[expose] noncomputable def anyMaskB (d : Nat) (f : Nat → Bool) : Bool :=
  !(allN (Nat.pow (nat_lit 2) d) fun mask => !(f mask))

@[expose] noncomputable def centB (w m : Nat) (bs L : List Nat) (T : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun b _ ih => bAnd(commB w m bs T b, ih)) L

@[expose] noncomputable def normB (w m : Nat) (bs L : List Nat) (T : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun b _ ih => bAnd(anyMaskB L.length fun mask => spanCompB w m bs L T b T mask, ih)) L

end CFSG.KS.PEnumB

end
