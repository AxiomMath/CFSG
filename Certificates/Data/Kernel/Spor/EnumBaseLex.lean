module

public import Certificates.Data.Kernel.Spor.EnumBase

public section

namespace CFSG.KS.EnumBase

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PEnum

@[expose] noncomputable def lexPosK (k cnt : Nat) (PL POS : Nat → Nat) (i : Nat) : Bool :=
  bAnd(bIf(Nat.beq i (nat_lit 0), true, bIf(Nat.blt (Nat.succ i) cnt,
      lexLtK (parOf PL i) (labOf PL i) (parOf PL (Nat.succ i)) (labOf PL (Nat.succ i)), true)),
    allN k (fun j => strictB (r32 POS (Nat.add (Nat.mul i k) j)) (fun q =>
      bIf(Nat.beq q (nat_lit 0), true,
        bIf(lexLtK i j (parOf PL q) (labOf PL q), false, true)))))

end CFSG.KS.EnumBase

end
