module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum

@[expose] noncomputable def lane5 (x j : Nat) : Nat :=
  fld(x, Nat.mul (nat_lit 16) j, nat_lit 65535)

@[expose] noncomputable def canon5 (x : Nat) : Bool :=
  bAnd(Nat.beq (Nat.shiftRight x (nat_lit 2128)) (nat_lit 0),
    allN (nat_lit 133) (fun j => Nat.blt (lane5 x j) (nat_lit 5)))

@[expose] noncomputable def red5 (x : Nat) : Nat :=
  foldN (nat_lit 133) (fun j acc => Nat.lor acc
    (Nat.shiftLeft (Nat.mod (lane5 x j) (nat_lit 5)) (Nat.mul (nat_lit 16) j))) (nat_lit 0)

@[expose] noncomputable def vm5 (Y : Nat → Nat) (x : Nat) : Nat :=
  strictN x (fun x => red5 (foldN (nat_lit 133) (fun j acc =>
    strictN (lane5 x j) (fun a => nIf(Nat.beq a (nat_lit 0), acc,
      Nat.add acc (Nat.mul a (Y j))))) (nat_lit 0)))

@[expose] noncomputable def slice5 (T : Nat → Nat) (k i : Nat) : Nat :=
  T (Nat.add (Nat.mul k (nat_lit 133)) i)

@[expose] noncomputable def entryOK (MT OP L R : Nat → Nat) (k b : Nat) : Bool :=
  strictB (L k) (fun l => strictB (R k) (fun r =>
    allBlk (Nat.mul (nat_lit 19) b) (fun i =>
      Nat.beq (nIf(Nat.beq (OP k) (nat_lit 0), vm5 (slice5 MT r) (slice5 MT l i),
        slice5 MT l i)) (slice5 MT k i)) (nat_lit 19)))

@[expose] noncomputable def canonAll (MT : Nat → Nat) (k : Nat) : Bool :=
  allN (nat_lit 133) (fun i => canon5 (slice5 MT k i))

@[expose] noncomputable def ws5 (c : Nat) : Bool :=
  bIf(Nat.beq c (nat_lit 32), true, bIf(Nat.beq c (nat_lit 9), true, bIf(Nat.beq c (nat_lit 10), true,
    bIf(Nat.beq c (nat_lit 13), true, bIf(Nat.beq c (nat_lit 11), true, Nat.beq c (nat_lit 12))))))

@[expose] noncomputable def ent5 (c : Nat) : Nat :=
  nIf(bAnd(Nat.ble (nat_lit 48) c, Nat.ble c (nat_lit 57)),
    Nat.mod (Nat.sub c (nat_lit 48)) (nat_lit 5), nat_lit 0)

@[expose] noncomputable def pay5Run (R : Nat → Nat) (cs : List Char) : Nat → Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat → Bool)
    (fun _ i _ acc => bIf(Nat.blt i (nat_lit 133),
      bAnd(Nat.beq (R i) acc,
        allBlk (Nat.succ i) (fun r => Nat.beq (R r) (nat_lit 0)) (Nat.sub (nat_lit 132) i)),
      true))
    (fun ch _ ih ph i j acc => strictB (Char.toNat ch) (fun c =>
      bIf(Nat.beq ph (nat_lit 0),
        bIf(Nat.beq c (nat_lit 10), ih (nat_lit 1) i j acc, ih (nat_lit 0) i j acc),
        bIf(ws5 c, ih (nat_lit 1) i j acc,
          bIf(Nat.blt i (nat_lit 133),
            strictB (Nat.lor acc (Nat.shiftLeft (ent5 c) (Nat.mul (nat_lit 16) j))) (fun acc' =>
              bIf(Nat.beq (Nat.succ j) (nat_lit 133),
                bAnd(Nat.beq (R i) acc', strictB (Nat.succ i) (fun i' =>
                  ih (nat_lit 1) i' (nat_lit 0) (nat_lit 0))),
                strictB (Nat.succ j) (fun j' => ih (nat_lit 1) i j' acc'))),
            ih (nat_lit 1) i j acc)))))
    cs

@[expose] noncomputable def pay5K (R : Nat → Nat) (cs : List Char) : Bool :=
  pay5Run R cs (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def idRow5 (i : Nat) : Nat := Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 16) i)

end CFSG.KS.SporSch

end
