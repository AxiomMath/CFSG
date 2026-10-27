module

public import Certificates.Data.Kernel.Spor.Mathieu

public section

namespace CFSG.KS.SporSch.Tern

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu

@[expose] noncomputable def ent (P i j : Nat) : Nat :=
  fld(P, Nat.mul (nat_lit 2) (Nat.add (Nat.mul (nat_lit 12) i) j), nat_lit 3)

@[expose] noncomputable def dig (b i : Nat) : Nat := Nat.mod (Nat.div b (Nat.pow (nat_lit 3) i)) (nat_lit 3)

@[expose] noncomputable def cw (P b j : Nat) : Nat :=
  Nat.mod (foldN (nat_lit 6) (fun i s => Nat.add s (Nat.mul (dig b i) (ent P i j))) (nat_lit 0))
    (nat_lit 3)

@[expose] noncomputable def supp (P b : Nat) : Nat :=
  foldN (nat_lit 12) (fun j s => nIf(Nat.beq (cw P b j) (nat_lit 0), s,
    Nat.lor s (Nat.shiftLeft (nat_lit 1) j))) (nat_lit 0)

@[expose] noncomputable def pop12 (x : Nat) : Nat :=
  foldN (nat_lit 12) (fun j s => Nat.add s (fld(x, j, nat_lit 1))) (nat_lit 0)

@[expose] noncomputable def wt (P b : Nat) : Nat := pop12 (supp P b)

@[expose] noncomputable def cnt (P n : Nat) : Nat :=
  foldN (nat_lit 729) (fun b s => nIf(Nat.beq (wt P b) n, Nat.succ s, s)) (nat_lit 0)

@[expose] noncomputable def memL (x : Nat) (S : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun y _ ih => bIf(Nat.beq x y, true, ih)) S

@[expose] noncomputable def incL (S : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun y _ ih p => bAnd(Nat.ble p y, ih (Nat.succ y))) S

@[expose] noncomputable def cntS (F : Nat) (S : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun s _ ih => nIf(Nat.beq (Nat.land F s) F, Nat.succ ih, ih)) S

@[expose] noncomputable def rowOK (P i : Nat) (r : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun j => Nat.beq j (nat_lit 12))
    (fun x _ ih j => bAnd(Nat.blt x (nat_lit 3), bAnd(Nat.beq x (ent P i j), ih (Nat.succ j)))) r
    (nat_lit 0)

@[expose] noncomputable def rowsOK (P : Nat) (rows : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun i => Nat.beq i (nat_lit 6))
    (fun r _ ih i => bAnd(rowOK P i r, ih (Nat.succ i))) rows (nat_lit 0)

@[expose] noncomputable def ternK (rows : List (List Nat)) (P : Nat) (C S : List Nat) : Bool :=
  bAnd(rowsOK P rows,
  bAnd(allN (nat_lit 13) (fun n => Nat.beq (cnt P n) (nget C n)),
  bAnd(allN (nat_lit 729) (fun b => bIf(Nat.beq (wt P b) (nat_lit 6), memL (supp P b) S, true)),
  bAnd(List.rec (motive := fun _ => Bool) true (fun s _ ih => bAnd(
      bIf(allN (nat_lit 729) (fun b => bIf(bAnd(Nat.beq (wt P b) (nat_lit 6), Nat.beq (supp P b) s),
        false, true)), false, true), ih)) S,
  bAnd(incL S (nat_lit 0),
    allN (nat_lit 4096) (fun F => bIf(Nat.beq (pop12 F) (nat_lit 5),
      Nat.beq (cntS F S) (nat_lit 1), true)))))))

end CFSG.KS.SporSch.Tern

end
