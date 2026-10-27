module

public import Certificates.Data.Kernel.Spor.F3Lane

public section

namespace CFSG.KS.F3L

open CFSG.F3.Native CFSG.KC.Enum

@[expose] noncomputable def bitK (x j : Nat) : Nat := Nat.land (Nat.shiftRight x j) (nat_lit 1)

@[expose] noncomputable def entR (rp rm j e : Nat) : Bool :=
  strictB (Nat.mod e (nat_lit 3)) fun t =>
    bAnd(Nat.beq (bitK rp j) nIf(Nat.beq t (nat_lit 1), nat_lit 1, nat_lit 0),
      Nat.beq (bitK rm j) nIf(Nat.beq t (nat_lit 2), nat_lit 1, nat_lit 0))

@[expose] noncomputable def rowAt (d P M i : Nat) (k : Nat → Nat → Bool) : Bool :=
  strictB (Nat.land (Nat.shiftRight P (Nat.mul d i)) (mk d)) fun a =>
    strictB (Nat.land (Nat.shiftRight M (Nat.mul d i)) (mk d)) fun b => k a b

@[expose] noncomputable def rowsBody (d P M : Nat) (cs : List Char) :
    Nat → Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat → Bool)
    (fun i _ _ _ => Nat.ble d i)
    (fun ch _ ih i j rp rm => strictB (Char.toNat ch) fun c =>
      bIf(wsK c, ih i j rp rm,
        bIf(Nat.blt i d,
          bAnd(entR rp rm j (entK c),
            strictB (Nat.succ j) fun j' =>
              bIf(Nat.beq j' d,
                strictB (Nat.succ i) fun i' => rowAt d P M i' (ih i' (nat_lit 0)),
                ih i j' rp rm)),
          true)))
    cs

@[expose] noncomputable def rowsHead (d P M : Nat) (cs : List Char) : Bool :=
  List.rec (motive := fun _ => Bool) (Nat.ble d (nat_lit 0))
    (fun ch rest ih => bIf(Nat.beq (Char.toNat ch) (nat_lit 10),
      rowAt d P M (nat_lit 0) (rowsBody d P M rest (nat_lit 0) (nat_lit 0)), ih)) cs

@[expose] noncomputable def seedRowsK (d : Nat) (L : V) (cs : List Char) : Bool :=
  strictB L.p fun P => strictB L.m fun M => rowsHead d P M cs

end CFSG.KS.F3L

end
