module

public import Certificates.Data.Kernel.SporSch.TitsPrim

public section

namespace CFSG.KC.MergeG

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch

@[expose] noncomputable def stepCG (n w kG : Nat) (GS : Nat → Nat) (S TP PP : Nat)
    (A : Nat → Nat) (s k i u v : Nat) : Bool :=
  bAnd(Nat.blt i kG, bAnd(Nat.blt u n, bAnd(Nat.blt v n,
  strictB (rootC n w S TP PP A s k u) (fun ru => strictB (rootC n w S TP PP A s k v) (fun rv =>
  strictB (rootC n w S TP PP A s k (pgW w (GS i) u)) (fun lp =>
  strictB (rootC n w S TP PP A s k (pgW w (GS i) v)) (fun lq =>
  bAnd(isRoot n TP k ru, bAnd(isRoot n TP k rv, bAnd(Nat.beq ru rv,
  bAnd(isRoot n TP k lp, bAnd(isRoot n TP k lq, bIf(Nat.beq lq lp, true,
    bAnd(Nat.beq (pgW 12 TP lq) k, Nat.beq (pgW w PP lq) lp))))))))))))))

@[expose] noncomputable def segCG (n w kG : Nat) (GS : Nat → Nat) (Lc S TP PP : Nat)
    (A RI RU RV : Nat → Nat) (s : Nat) : Bool :=
  strictB (Nat.mul S s) (fun k0 => strictB (Nat.min (Nat.add k0 S) Lc) (fun ke =>
  bAnd(allN (Nat.sub ke k0) (fun t => stepCG n w kG GS S TP PP A s (Nat.add k0 t)
    (RI (Nat.add k0 t)) (RU (Nat.add k0 t)) (RV (Nat.add k0 t))),
  allN n (fun y => Nat.beq (pgW w (A (Nat.succ s)) y) (findK n w TP PP ke (Nat.succ S)
    (pgW w (A s) y))))))

@[expose] noncomputable def mergeCKG (n w kG : Nat) (GS : Nat → Nat) (b x Lc S NS : Nat)
    (RI RU RV : Nat → Nat) (TP PP : Nat) (A : Nat → Nat) : Bool :=
  bAnd(Nat.blt b n, bAnd(Nat.blt x n, bAnd(Nat.blt Lc 4096, bAnd(Nat.blt 0 S,
  bAnd(Nat.ble Lc (Nat.mul S NS),
  bAnd(allN n (fun y => Nat.beq (pgW w (A 0) y) (nIf(Nat.beq y x, b, y))),
  bAnd(allN NS (segCG n w kG GS Lc S TP PP A RI RU RV),
  bAnd(allN n (fun l => Nat.ble (pgW 12 TP l) Lc),
  bAnd(Nat.beq (mergeCnt n w GS Lc S TP PP A RI RU RV) (timedCnt n Lc TP),
    finalC n w Lc NS TP A)))))))))

end CFSG.KC.MergeG

end
