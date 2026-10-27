module

public import Certificates.Data.Kernel.TitsOctK
public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.TitsOctLamK

open CFSG.KC.Enum CFSG.KS CFSG.KC.TwoF4LieK CFSG.KC.TitsOctK

@[expose] noncomputable def midL (LAY x : Nat) : Bool :=
  bAnd(Nat.blt 0 (layAt LAY x), Nat.blt (layAt LAY x) (nat_lit 8))

@[expose] noncomputable def layCnt (LAY c : Nat) : Nat :=
  CFSG.KC.Loop.sumBelow (nat_lit 1755) (nat_lit 28)
    (fun x => nIf(Nat.beq (layAt LAY x) c, nat_lit 1, nat_lit 0))

@[expose] noncomputable def lamCnt (L0 LJ : Nat) : Nat :=
  CFSG.KC.Loop.sumBelow (nat_lit 1755) (nat_lit 28)
    (fun x => nIf(bAnd(Nat.beq (layAt L0 x) (nat_lit 8), midL LJ x), nat_lit 1, nat_lit 0))

@[expose] noncomputable def recPK (A : Nat → Nat) (k root cnt LAY l ORD PR LB PS : Nat) : Bool :=
  bAnd(Nat.beq (fw (nat_lit 13) ORD 0) root, bAnd(Nat.blt root (nat_lit 1755),
  bAnd(allN cnt (fun i => strictB (fw (nat_lit 13) ORD i) (fun x => bAnd(Nat.blt x (nat_lit 1755),
    bIf(Nat.beq i (nat_lit 0), true, strictB (fw (nat_lit 11) PR i) (fun p =>
      strictB (fw (nat_lit 3) LB i) (fun j => bAnd(Nat.blt p i, bAnd(Nat.blt j k,
        Nat.beq (gp (A j) (fw (nat_lit 13) ORD p)) x)))))))),
    allN (nat_lit 1755) (fun x => bIf(Nat.beq (layAt LAY x) l,
      strictB (fw (nat_lit 13) PS x) (fun q => bAnd(Nat.blt q cnt, Nat.beq (fw (nat_lit 13) ORD q) x)),
      true)))))

@[expose] noncomputable def cmpK (L0 LX LY : Nat) : Bool :=
  allN (nat_lit 1755) (fun c => bIf(Nat.beq (layAt L0 c) (nat_lit 8),
    bIf(midL LY c, bIf(midL LX c, false, true), midL LX c), true))

@[expose] noncomputable def adjP (lp : Nat → Nat) : List Nat → Bool :=
  List.rec (motive := fun _ => Bool) true (fun a t ih =>
    bAnd(List.rec (motive := fun _ => Bool) true (fun b _ _ => adjK lp a b) t, ih))

@[expose] noncomputable def walkK (lp : Nat → Nat) (L0 LX : Nat) (P : List Nat) : Bool :=
  bAnd(Nat.blt 0 P.length, bAnd(Nat.ble P.length (nat_lit 8), bAnd(adjP lp P,
    strictB (P.getLastD 0) (fun c => bAnd(Nat.blt c (nat_lit 1755),
      bAnd(Nat.beq (layAt L0 c) (nat_lit 8), midL LX c))))))

@[expose] noncomputable def starts (L0 xp : Nat) (W : List (List Nat)) : Bool :=
  allN (nat_lit 1755) (fun y => bIf(Nat.beq (layAt L0 y) (nat_lit 2), bIf(Nat.beq y xp, true,
    List.rec (motive := fun _ => Bool) false (fun P _ ih => bIf(Nat.beq (P.headD 0) y, true, ih)) W),
    true))

end CFSG.KC.TitsOctLamK

end
