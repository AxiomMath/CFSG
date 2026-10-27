module

public import Certificates.Data.Kernel.Spor.Text

public section

namespace CFSG.KS.HexNums

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def hexL (c : Nat) : Nat :=
  nIf(Nat.blt c (nat_lit 48), nat_lit 16, nIf(Nat.blt c (nat_lit 58), Nat.sub c (nat_lit 48),
    nIf(Nat.blt c (nat_lit 97), nat_lit 16, nIf(Nat.blt c (nat_lit 103), Nat.sub c (nat_lit 87),
      nat_lit 16))))

@[expose] noncomputable def run (d w N F : Nat) (cs : List Char) : Nat → Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat → Bool)
    (fun k _ _ acc => bAnd(Nat.beq k N, Nat.beq acc F))
    (fun ch _ ih k t v acc => strictB (hexL (Char.toNat ch)) (fun h =>
      bIf(Nat.blt h (nat_lit 16),
        strictB (Nat.add (Nat.mul v (nat_lit 16)) h) (fun v' =>
        bIf(Nat.beq (Nat.succ t) d,
          bIf(Nat.blt v' (Nat.shiftLeft (nat_lit 1) w),
            ih (Nat.succ k) (nat_lit 0) (nat_lit 0) (Nat.lor acc (Nat.shiftLeft v' (Nat.mul w k))),
            false),
          ih k (Nat.succ t) v' acc)),
        ih k t v acc)))
    cs

@[expose] noncomputable def hexNumsK (cs : List Char) (d w N F : Nat) : Bool :=
  bAnd(Nat.blt (nat_lit 0) d, run d w N F cs (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0))

end CFSG.KS.HexNums

end
