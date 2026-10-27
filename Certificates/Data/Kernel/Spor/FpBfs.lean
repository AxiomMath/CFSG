module

public import Certificates.Data.Kernel.Spor.Prim

public section

namespace CFSG.KS.FpBfs

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim

@[expose] noncomputable def fpOf (f : Nat → Nat) : Nat :=
  Nat.add (f (nat_lit 17)) (Nat.mul (nat_lit 1782) (Nat.add (f (nat_lit 333))
    (Nat.mul (nat_lit 1782) (Nat.add (f (nat_lit 901)) (Nat.mul (nat_lit 1782)
      (Nat.add (f (nat_lit 1500)) (Nat.mul (nat_lit 1782) (Nat.add (f (nat_lit 1234))
        (Nat.mul (nat_lit 1782) (f (nat_lit 77)))))))))))

@[expose] noncomputable def fpK (w m T : Nat) : Nat := fpOf (fun i => pg w m T i)

@[expose] noncomputable def fpCK (w m G GI T : Nat) : Nat :=
  fpOf (fun i => pg w m G (pg w m T (pg w m GI i)))

@[expose] noncomputable def fpBfsHdK (n w m nw k M cnt E R : Nat) (G GI T PL FP : Nat → Nat) :
    Bool :=
  bAnd(Nat.blt (nat_lit 1) cnt, bAnd(Nat.blt (nat_lit 0) k,
  bAnd(Nat.beq (T (nat_lit 0)) R, bAnd(canonK n w m nw R,
  bAnd(allN k (fun s => bAnd(canonK n w m nw (G s), canonK n w m nw (GI s))),
  bAnd(Nat.beq E (Nat.succ (PL (Nat.pred cnt))),
  bAnd(Nat.blt (Nat.div (PL (Nat.pred cnt)) k) M,
  bAnd(Nat.beq (FP (nat_lit 0)) (fpK w m R),
    allN cnt (fun i => strictB (FP i) (fun f =>
      allN i (fun j => bIf(Nat.beq f (FP j), false, true))))))))))))

@[expose] noncomputable def fpBfsPtK (n w m nw k cnt : Nat) (G GI T V PL FP : Nat → Nat)
    (i : Nat) : Bool :=
  strictB (PL i) (fun c => strictB (Nat.div c k) (fun h => strictB (Nat.mod c k) (fun s =>
  bAnd(Nat.blt h i, bAnd(compEqK n w m nw (T h) (GI s) (V i),
  bAnd(compEqK n w m nw (G s) (V i) (T i), bAnd(Nat.beq (FP i) (fpK w m (T i)),
    bIf(Nat.blt (Nat.succ i) cnt, Nat.blt c (PL (Nat.succ i)), true))))))))

@[expose] noncomputable def fpBfsStK (w m k cnt : Nat) (G GI T PL POS FP : Nat → Nat) (e : Nat) :
    Bool :=
  strictB (POS e) (fun j => strictB (Nat.mod e k) (fun s =>
  bAnd(Nat.blt j cnt, bAnd(Nat.beq (FP j) (fpCK w m (G s) (GI s) (T (Nat.div e k))),
    bIf(Nat.beq j (nat_lit 0), true, Nat.ble (PL j) e)))))

@[expose] noncomputable def fpBfsPtSlK (n w m nw k cnt : Nat) (G GI T V PL FP : Nat → Nat)
    (lo len : Nat) : Bool :=
  allN len (fun d => strictB (Nat.add lo d) (fun i =>
    bIf(Nat.blt i cnt, bIf(Nat.beq i (nat_lit 0), true, fpBfsPtK n w m nw k cnt G GI T V PL FP i),
      true)))

@[expose] noncomputable def fpBfsStSlK (w m k cnt E : Nat) (G GI T PL POS FP : Nat → Nat)
    (lo len : Nat) : Bool :=
  allN len (fun d => strictB (Nat.add lo d) (fun e =>
    bIf(Nat.blt e E, fpBfsStK w m k cnt G GI T PL POS FP e, true)))

end CFSG.KS.FpBfs

end
