module

public import Certificates.Data.Kernel.SporSch.HNF5

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum

@[expose] noncomputable def krConst (v s : Nat) : Nat :=
  foldN (nat_lit 133) (fun d acc => Nat.add acc (Nat.shiftLeft v (Nat.mul (Nat.mul (nat_lit 16) s) d)))
    (nat_lit 0)

@[expose] noncomputable def krSpr (S M r : Nat) : Nat := Nat.land (Nat.mul r S) M

@[expose] noncomputable def krCol (S M : Nat) (Y : Nat → Nat) : Nat :=
  foldN (nat_lit 133) (fun j acc => Nat.add acc
    (Nat.shiftLeft (krSpr S M (Y j)) (Nat.mul (nat_lit 16) (Nat.sub (nat_lit 132) j)))) (nat_lit 0)

@[expose] noncomputable def krRow (S M F Q cs x c : Nat) : Bool :=
  strictB (Nat.land (Nat.shiftRight (Nat.mul x cs) (nat_lit 2112)) M) fun u =>
  strictB (krSpr S M c) fun sc =>
  strictB (Nat.sub (Nat.add u F) sc) fun D =>
  strictB (Nat.div D (nat_lit 5)) fun q =>
    bAnd(Nat.ble sc (Nat.add u F), bAnd(Nat.beq (Nat.mul q (nat_lit 5)) D,
      Nat.beq (Nat.land q Q) q))

@[expose] noncomputable def krCanon (M8 K3 x : Nat) : Bool :=
  bAnd(Nat.beq (Nat.shiftRight x (nat_lit 2128)) (nat_lit 0), bAnd(Nat.beq (Nat.land x M8) (nat_lit 0),
    Nat.beq (Nat.land (Nat.add x K3) M8) (nat_lit 0)))

@[expose] noncomputable def krProd (S M F Q : Nat) (Y X C : Nat → Nat) : Bool :=
  strictB (krCol S M Y) fun cs => allN (nat_lit 133) fun i => krRow S M F Q cs (X i) (C i)

@[expose] noncomputable def krEnt (S M F Q M8 K3 : Nat) (MT OP L R : Nat → Nat) (k : Nat) : Bool :=
  strictB (OP k) fun op => strictB (L k) fun l => strictB (R k) fun r =>
    bAnd(allN (nat_lit 133) (fun i => krCanon M8 K3 (slice5 MT k i)),
      bIf(Nat.beq op (nat_lit 0), krProd S M F Q (slice5 MT r) (slice5 MT l) (slice5 MT k),
        bIf(Nat.beq op (nat_lit 1),
          allN (nat_lit 133) (fun i => Nat.beq (slice5 MT l i) (slice5 MT k i)), true)))

@[expose] noncomputable def krBlk (MT OP L R : Nat → Nat) (a n : Nat) : Bool :=
  strictB (krConst (nat_lit 1) (nat_lit 264)) fun S =>
  strictB (krConst (nat_lit 65535) (nat_lit 265)) fun M =>
  strictB (krConst (nat_lit 5) (nat_lit 265)) fun F =>
  strictB (krConst (nat_lit 4095) (nat_lit 265)) fun Q =>
  strictB (krConst (nat_lit 65528) (nat_lit 1)) fun M8 =>
  strictB (krConst (nat_lit 3) (nat_lit 1)) fun K3 =>
    allBlk a (krEnt S M F Q M8 K3 MT OP L R) n

end CFSG.KS.SporSch

end
