module

public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KC.J2Orb

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def lenK {α : Type} (l : List α) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) l

@[expose] noncomputable def allLtL (p : Nat) (v : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => bAnd(Nat.blt x p, ih)) v

@[expose] noncomputable def wfMK (p d : Nat) (X : List (List Nat)) : Bool :=
  bAnd(Nat.beq (lenK X) d,
    List.rec (motive := fun _ => Bool) true
      (fun r _ ih => bAnd(Nat.beq (lenK r) d, bAnd(allLtL p r, ih))) X)

@[expose] noncomputable def codeL (v : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun x _ ih s => Nat.lor (Nat.shiftLeft x s) (ih (Nat.add s (nat_lit 3)))) v (nat_lit 0)

@[expose] noncomputable def dotK (p : Nat) (r : List Nat) (v : Nat) : Nat :=
  Nat.mod (List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun a _ ih k => Nat.add (Nat.mul a (pg (nat_lit 3) (nat_lit 7) v k)) (ih (Nat.succ k))) r
    (nat_lit 0)) p

@[expose] noncomputable def mvK (p : Nat) (X : List (List Nat)) (v : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun r _ ih s => Nat.lor (Nat.shiftLeft (dotK p r v) s) (ih (Nat.add s (nat_lit 3)))) X
    (nat_lit 0)

@[expose] noncomputable def stepC (c a : Nat) : Nat :=
  nIf(Nat.beq c (nat_lit 0), nat_lit 0, nIf(Nat.blt a c, c, nIf(Nat.beq a c, Nat.succ c, nat_lit 0)))

@[expose] noncomputable def bfsCnt (N ALP BEP : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 1)
    (fun h c => strictN c (fun c' => nIf(Nat.blt h c',
      strictN (stepC c' (pg (nat_lit 9) (nat_lit 511) ALP h)) (fun c2 =>
        stepC c2 (pg (nat_lit 9) (nat_lit 511) BEP h)), nat_lit 0))) N

@[expose] noncomputable def orbK (p d cap N : Nat) (A B : List (List Nat)) (root : List Nat)
    (PTP ALP BEP : Nat) : Bool :=
  strictB (Nat.mul (nat_lit 3) d) (fun cw => strictB (mask cw) (fun cm =>
  bAnd(Nat.ble p (nat_lit 8), bAnd(Nat.ble (nat_lit 1) N, bAnd(Nat.ble N cap,
  bAnd(Nat.blt N (nat_lit 512),
  bAnd(wfMK p d A, bAnd(wfMK p d B, bAnd(Nat.beq (lenK root) d, bAnd(allLtL p root,
  bAnd(Nat.beq (codeL root) (pg cw cm PTP (nat_lit 0)),
  bAnd(allN N (fun i => strictB (pg cw cm PTP i) (fun v =>
    strictB (pg (nat_lit 9) (nat_lit 511) ALP i) (fun a =>
    strictB (pg (nat_lit 9) (nat_lit 511) BEP i) (fun b =>
    bAnd(Nat.blt a N, bAnd(Nat.blt b N,
    bAnd(Nat.beq (mvK p A v) (pg cw cm PTP a), Nat.beq (mvK p B v) (pg cw cm PTP b)))))))),
  bAnd(allN N (fun i => strictB (pg cw cm PTP i) (fun v =>
    allN i (fun j => bIf(Nat.beq v (pg cw cm PTP j), false, true)))),
  Nat.beq (bfsCnt N ALP BEP) N)))))))))))))

end CFSG.KC.J2Orb

end
