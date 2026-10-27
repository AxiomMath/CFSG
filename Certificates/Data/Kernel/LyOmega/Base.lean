module

public import Certificates.Data.Kernel.LyOmega.Chart
public import Certificates.Data.Kernel.LyOmega.Small

public section

namespace CFSG.KC.LyOm

open CFSG.KC.Loop CFSG.KC.LL CFSG.KC.Ord

@[expose] noncomputable def fTr (X : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => strictN acc (fun a => Nat.lor a
      (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
        (fun j acc2 => Nat.lor acc2 (Nat.shiftLeft (bEnt X i j)
          (Nat.add (Nat.mul (nat_lit 1332) j) (Nat.mul (nat_lit 12) i)))) (nat_lit 111))))
    (nat_lit 111)

@[expose] noncomputable def toBig (X : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun t acc => (fun i j => Nat.lor acc (Nat.shiftLeft (sEnt X i j)
        (Nat.add (Nat.mul (nat_lit 1332) i) (Nat.mul (nat_lit 12) j))))
      (Nat.div t (nat_lit 7)) (Nat.mod t (nat_lit 7))) (nat_lit 49)

@[expose] noncomputable def relayOK (X Y : Nat) : Bool :=
  bAnd(Nat.beq (Nat.shiftRight Y (nat_lit 539)) (nat_lit 0),
    Nat.rec (motive := fun _ => Bool) true
      (fun t ih => bAnd((fun i j => Nat.beq (bEnt X i j) (sEnt Y i j))
        (Nat.div t (nat_lit 7)) (Nat.mod t (nat_lit 7)), ih)) (nat_lit 49))

@[expose] noncomputable def fWord (C : BConsts) (G : Nat → Nat) (X : Nat) (w : List Nat) : Nat :=
  wordR (fMul C) G X w

@[expose] noncomputable def bWord (C : BConsts) (G : Nat → Nat) (X : Nat) (w : List Nat) : Nat :=
  wordR (bMul C) G X w

@[expose] noncomputable def sWord (C : SConsts) (G : Nat → Nat) (X : Nat) (w : List Nat) : Nat :=
  wordR (sMul C) G X w

@[expose] noncomputable def digLanesRun (X : Nat) (cs : List Char) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun i => i)
    (fun ch _ ih i => strictN (Char.toNat ch) (fun c =>
      nIf(Nat.beq c (nat_lit 10), ih i,
        nIf(bAnd(Nat.ble (nat_lit 48) c, bAnd(Nat.ble c (nat_lit 57),
            Nat.beq (Nat.sub c (nat_lit 48))
              (bEnt X (Nat.div i (nat_lit 111)) (Nat.mod i (nat_lit 111))))),
          ih (Nat.succ i), nat_lit 1048576))))
    cs

@[expose] noncomputable def digLanesK (cs : List Char) (X n : Nat) : Bool :=
  Nat.beq (digLanesRun X cs (nat_lit 0)) n

@[expose] noncomputable def tabPI (C : BConsts) (PI PJ : Nat → Nat) (nc : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun c ih => bAnd(bIf(Nat.blt c nc,
      bAnd(fVld C (PI c), bAnd(fVld C (PJ c), Nat.beq (fMul C (PI c) (PJ c)) C.ONEF)), true), ih))
    (nat_lit 8)

@[expose] noncomputable def tabGT (C : BConsts) (PI GT : Nat → Nat) (G0 G1 nc lo cnt : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun j ih => bAnd(
    (fun k => (fun s c c' => bIf(bAnd(Nat.blt c nc, Nat.blt c' nc),
        bAnd(fVld C (GT k), Nat.beq (fMul C (PI c) (GT k)) (fMul C (pickL [G0, G1] s) (PI c'))), true))
      (Nat.mod k 2) (Nat.mod (Nat.div k 2) 8) (Nat.div k 16)) (Nat.add lo j), ih)) cnt

@[expose] noncomputable def tabWC (C : BConsts) (PI WC : Nat → Nat) (nc : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => bAnd(
    (fun c e => bIf(bAnd(Nat.blt e c, Nat.blt c nc),
        bAnd(fVld C (WC k), Nat.beq (fMul C (PI c) (WC k)) (PI e)), true))
      (Nat.mod k 8) (Nat.div k 8), ih)) (nat_lit 64)

@[expose] noncomputable def tabX (C : BConsts) (PI XM : Nat → Nat) (P nc : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun c ih => bAnd(bIf(Nat.blt c nc,
      bAnd(fVld C (XM c), Nat.beq (fMul C (PI c) (XM c)) (fMul C P (PI c))), true), ih)) (nat_lit 8)

@[expose] noncomputable def rootOK (C : BConsts) (KX PT PI : Nat → Nat) (Z : Nat) : Bool :=
  sameSpanL C (getRec KX (nat_lit 9324) (nat_lit 0))
    (bMul C Z (PI (chartOf (getRec PT (nat_lit 32) (nat_lit 0)))))

@[expose] noncomputable def rootFix (C : BConsts) (KX PT PI PJ G : Nat → Nat) (w : List Nat) : Bool :=
  letB (chartOf (getRec PT (nat_lit 32) (nat_lit 0))) (fun c =>
    sameSpanL C (getRec KX (nat_lit 9324) (nat_lit 0))
      (bMul C (bWord C G (bMul C (getRec KX (nat_lit 9324) (nat_lit 0)) (PJ c)) (List.reverse w)) (PI c)))

end CFSG.KC.LyOm

end
