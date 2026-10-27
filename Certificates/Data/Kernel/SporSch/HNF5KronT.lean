module

public import Certificates.Data.Kernel.SporSch.HNF5Kron

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum

@[expose] noncomputable def krColF (S M : Nat) (Y : Nat → Nat) : Nat :=
  foldN (nat_lit 133) (fun j acc => Nat.add acc
    (Nat.shiftLeft (krSpr S M (Y j)) (Nat.mul (nat_lit 16) j))) (nat_lit 0)

@[expose] noncomputable def krRowF (X : Nat → Nat) : Nat :=
  foldN (nat_lit 133) (fun c acc => Nat.add acc
    (Nat.shiftLeft (X c) (Nat.mul (nat_lit 4240) c))) (nat_lit 0)

@[expose] noncomputable def krEntT (S M F Q M8 K3 : Nat) (MT OP L R : Nat → Nat) (k : Nat) : Bool :=
  strictB (OP k) fun op => strictB (L k) fun l => strictB (R k) fun r =>
    bAnd(allN (nat_lit 133) (fun i => krCanon M8 K3 (slice5 MT k i)),
      bIf(Nat.beq op (nat_lit 0), krProd S M F Q (slice5 MT r) (slice5 MT l) (slice5 MT k),
        bIf(Nat.beq op (nat_lit 1),
          allN (nat_lit 133) (fun i => Nat.beq (slice5 MT l i) (slice5 MT k i)),
          bIf(Nat.beq op (nat_lit 3),
            Nat.beq (krColF S M (slice5 MT l)) (krRowF (slice5 MT k)), true))))

@[expose] noncomputable def krBlkT (MT OP L R : Nat → Nat) (a n : Nat) : Bool :=
  strictB (krConst (nat_lit 1) (nat_lit 264)) fun S =>
  strictB (krConst (nat_lit 65535) (nat_lit 265)) fun M =>
  strictB (krConst (nat_lit 5) (nat_lit 265)) fun F =>
  strictB (krConst (nat_lit 4095) (nat_lit 265)) fun Q =>
  strictB (krConst (nat_lit 65528) (nat_lit 1)) fun M8 =>
  strictB (krConst (nat_lit 3) (nat_lit 1)) fun K3 =>
    allBlk a (krEntT S M F Q M8 K3 MT OP L R) n

end CFSG.KS.SporSch

end
