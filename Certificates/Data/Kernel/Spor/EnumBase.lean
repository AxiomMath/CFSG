module

public import Certificates.Data.Kernel.Spor.BaseEq
public import Certificates.Data.Kernel.Spor.PEnum

public section

namespace CFSG.KS.EnumBase

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PEnum CFSG.KS.BaseEq

@[expose] noncomputable def recK (n w m ng : Nat) (G T PL : Nat → Nat) (k : Nat) : Bool :=
  strictB (T k) (fun t => bIf(Nat.beq k (nat_lit 0), Nat.beq t (pidn n w),
    strictB (parOf PL k) (fun p => strictB (labOf PL k) (fun l =>
      bAnd(Nat.blt p k, bAnd(Nat.blt l ng, Nat.beq t (pcomp n w m (G l) (T p))))))))

@[expose] noncomputable def leftK (w m : Nat) (ps : List Nat) (ng N : Nat) (G T POS : Nat → Nat)
    (k : Nat) : Bool :=
  strictB (T k) (fun t => allN ng (fun g => strictB (r32 POS (Nat.add (Nat.mul k ng) g)) (fun q =>
    bAnd(Nat.blt q N, left2K w m ps (G g) t (T q)))))

@[expose] noncomputable def classPtK (w m : Nat) (ps : List Nat) (ng N : Nat)
    (G GI T FL FP FG FQ MK PIX : Nat → Nat) (c o cnt j : Nat) : Bool :=
  strictB (FL (Nat.add o j)) (fun x => strictB (T x) (fun tx =>
  bAnd(Nat.blt x N, bAnd(Nat.beq (MK x) c, bAnd(Nat.beq (PIX x) j,
  bAnd(bIf(Nat.beq j (nat_lit 0), true,
    strictB (FP (Nat.add o j)) (fun p => strictB (FG (Nat.add o j)) (fun l =>
      bAnd(Nat.blt p j, bAnd(Nat.blt l ng, bAnd(conj3K w m ps (G l) (T (FL (Nat.add o p))) (GI l) tx,
        bIf(Nat.blt (Nat.succ j) cnt,
          lexLtK p l (FP (Nat.add o (Nat.succ j))) (FG (Nat.add o (Nat.succ j))), true))))))),
  allN ng (fun g => strictB (FQ (Nat.add (Nat.mul (Nat.add o j) ng) g)) (fun q =>
    bAnd(Nat.blt q cnt, bAnd(conj3K w m ps (G g) tx (GI g) (T (FL (Nat.add o q))),
      bIf(Nat.beq q (nat_lit 0), true,
        bIf(lexLtK j g (FP (Nat.add o q)) (FG (Nat.add o q)), false, true))))))))))))

@[expose] noncomputable def classK (w m : Nat) (ps : List Nat) (ng N : Nat)
    (G GI T FL FP FG FQ CO MK PIX : Nat → Nat) (c : Nat) : Bool :=
  strictB (CO c) (fun o => strictB (CO (Nat.succ c)) (fun o' => strictB (Nat.sub o' o) (fun cnt =>
    bAnd(Nat.ble o o', bAnd(Nat.blt (nat_lit 0) cnt, bAnd(Nat.ble cnt N,
    bAnd(Nat.beq (FP o) (nat_lit 0), bAnd(Nat.beq (FG o) (nat_lit 0),
    bAnd(sqFixK w m ps (T (FL o)),
      allN cnt (fun j => classPtK w m ps ng N G GI T FL FP FG FQ MK PIX c o cnt j))))))))))

@[expose] noncomputable def coverK (w m : Nat) (ps : List Nat) (nc : Nat) (T FL CO MK PIX : Nat → Nat)
    (k : Nat) : Bool :=
  bIf(sqFixK w m ps (T k), strictB (MK k) (fun c => bAnd(Nat.blt c nc,
    strictB (PIX k) (fun j => bAnd(Nat.blt j (Nat.sub (CO (Nat.succ c)) (CO c)),
      Nat.beq (FL (Nat.add (CO c) j)) k)))), true)

@[expose] noncomputable def sliceK (N L : Nat) (f : Nat → Bool) (s : Nat) : Bool :=
  allN L (fun d => strictB (Nat.add (Nat.mul L s) d) (fun i => bIf(Nat.blt i N, f i, true)))

@[expose] noncomputable def listFK (w : Nat) (P : Nat) (L : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih i => bAnd(Nat.beq x (pg w (mask w) P i), ih (Nat.succ i))) L

@[expose] noncomputable def iNat (z : Int) : Nat := Int.rec (motive := fun _ => Nat) (fun a => a)
  (fun _ => nat_lit 0) z

@[expose] noncomputable def fstN (r : List Int) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun z _ _ => iNat z) r

@[expose] noncomputable def sndN (r : List Int) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ zs _ => fstN zs) r

@[expose] noncomputable def parRK (PL : Nat → Nat) (L : List (List Int)) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun r _ ih i => bAnd(Nat.beq (fstN r) (parOf PL i), bAnd(Nat.beq (sndN r) (labOf PL i),
      ih (Nat.succ i)))) L

@[expose] noncomputable def posRK (POS : Nat → Nat) (ng g : Nat) (L : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih i => bAnd(Nat.beq x (r32 POS (Nat.add (Nat.mul i ng) g)), ih (Nat.succ i))) L

end CFSG.KS.EnumBase

end
