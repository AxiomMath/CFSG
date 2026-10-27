module

public import Certificates.Data.Kernel.Co1T13K

public section

namespace CFSG.KC.Co1T13K

open CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.KLie.CT

@[expose] noncomputable def selK (f : Nat → Nat) (a n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun k acc => nIf(bit a k, Nat.xor (f k) acc, acc)) n

@[expose] noncomputable def wK (YT : List Nat) (r s k : Nat) : Nat :=
  nIf(Nat.blt k (nat_lit 12), vmF (nat_lit 24) (getL (nat_lit 0) YT k) r,
    vmF (nat_lit 24) (getL (nat_lit 0) YT (Nat.sub k (nat_lit 12))) s)

@[expose] noncomputable def spanK (YT R0 R1 NT : List Nat) : Bool :=
  CFSG.KC.Enum.allN (nat_lit 12) fun i => CFSG.KC.Enum.allN (nat_lit 12) fun j =>
    CFSG.KC.Enum.allN (nat_lit 24) fun m =>
      Nat.beq (selK (wK YT (getL (nat_lit 0) R0 i) (getL (nat_lit 0) R1 j))
        (rowF (nat_lit 24) (getL (nat_lit 0) NT (Nat.add (Nat.mul (nat_lit 12) i) j)) m) (nat_lit 24))
        (Nat.shiftLeft (nat_lit 1) m)

end CFSG.KC.Co1T13K

end
