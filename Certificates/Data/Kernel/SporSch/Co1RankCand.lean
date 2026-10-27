module

public import Certificates.Data.Kernel.SporSch.Co1RankCoord

public section

namespace CFSG.KC.Co1RankCand

open CFSG.KC.Loop CFSG.KC.Co1RankCoord

structure Dat where
  d : Nat
  Kt : Nat
  NCt : Nat
  PHt : Nat
  T2A : List (List Nat)
  nU : Nat
  UC : Nat
  reps : List (List Nat × Nat × List (Nat × Nat × List Nat × List Nat))

@[expose] noncomputable def toC (D : Dat) : Co1RankCoord.Dat := ⟨D.d, D.Kt, D.NCt, D.PHt, 0, []⟩

@[expose] noncomputable def getLL (L : List (List Nat)) (k : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun a _ ih k => Nat.rec (motive := fun _ => List Nat) a (fun k' _ => ih k') k) L k

@[expose] noncomputable def in2A (D : Dat) (x : Nat) : Bool :=
  strictB (Nat.shiftRight x D.d) fun j =>
    Nat.beq (fld(getL (getLL D.T2A (Nat.shiftRight j 3)) (Nat.land j 7), Nat.land x (mask D.d), 1)) 1

@[expose] noncomputable def codeOK (D : Dat) (Ts : Nat) (El : List Nat) (nE y c : Nat) : Bool :=
  bIf(Nat.blt c nE, Nat.beq (getL El c) y,
  bIf(Nat.blt c (Nat.add nE nE), in2A D (mulC (toC D) (getL El (Nat.sub c nE)) y),
    strictB (Nat.sub c (Nat.add nE nE)) fun p =>
    strictB (Nat.mod p D.nU) fun u =>
    bAnd(Nat.beq (fld(D.UC, Nat.mul (Nat.add D.d 7) u, mask (Nat.add D.d 7))) y,
      Nat.beq (fld(Ts, p, 1)) 1)))

@[expose] noncomputable def codesOK (D : Dat) (Ts : Nat) (El : List Nat) (nE j : Nat) (K : List Nat)
    (q0 : Nat) (cs : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool)
    (fun idx => Nat.beq idx (Nat.shiftLeft 1 (lenL K)))
    (fun c _ ih idx => bAnd(codeOK D Ts El nE (Nat.lor (Nat.shiftLeft j D.d) (spanK K q0 idx)) c,
      strictB (Nat.succ idx) ih)) cs 0

@[expose] noncomputable def entryOK (D : Dat) (gs : List Nat) (Ts : Nat) (El : List Nat) (nE j : Nat)
    (e : Nat × Nat × List Nat × List Nat) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun mode r => Prod.rec (motive := fun _ => Bool) (fun a r =>
    Prod.rec (motive := fun _ => Bool) (fun K cs =>
      bIf(Nat.beq mode 3, bIf(Nat.beq (kt D.Kt j j) 0, false, true),
      bIf(Nat.beq mode 0,
        strictB (Nat.shiftRight (getL gs a) D.d) fun i =>
          bIf(Nat.beq (kt D.Kt i j) (kt D.Kt j i), false, Nat.blt a (lenL gs)),
      bAnd(Nat.beq (kt D.Kt j j) 0,
      strictB (Nat.mul D.d (Nat.succ (lenL gs))) fun W =>
      strictB (rowsF (toC D) j gs W) fun A =>
      strictB (rhs (toC D) j gs) fun B =>
      strictB (rankRC D.d W A) fun rk =>
      bIf(Nat.beq mode 2,
        Nat.beq (rankRC (Nat.succ D.d) W (Nat.lor A (Nat.shiftLeft B (Nat.mul W D.d)))) (Nat.succ rk),
      bAnd(Nat.beq mode 1,
      bAnd(Nat.beq (lhs (toC D) j gs a) B,
      bAnd(List.rec (motive := fun _ => Bool) true
        (fun k _ ih => bAnd(Nat.beq (lhs (toC D) j gs k) 0, ih)) K,
      bAnd(Nat.beq (Nat.add rk (lenL K)) D.d,
      bAnd(Nat.beq (rankRC (lenL K) D.d (packL D.d K)) (lenL K),
        codesOK D Ts El nE j K a cs)))))))))) r) r) e

@[expose] noncomputable def entriesOK (D : Dat) (gs : List Nat) (Ts : Nat) (El : List Nat) (nE : Nat)
    (es : List (Nat × Nat × List Nat × List Nat)) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun j => Nat.beq j 128)
    (fun e _ ih j => bAnd(entryOK D gs Ts El nE j e, strictB (Nat.succ j) ih)) es 0

@[expose] noncomputable def chkC (D : Dat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun p _ ih =>
    Prod.rec (motive := fun _ => Bool) (fun gs r => Prod.rec (motive := fun _ => Bool) (fun Ts es =>
      bAnd((fun El => entriesOK D gs Ts El (lenL El) es) (spanL (toC D) gs), ih)) r) p) D.reps

end CFSG.KC.Co1RankCand

end
