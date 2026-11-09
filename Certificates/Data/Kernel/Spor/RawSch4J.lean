module

public import Certificates.Data.Kernel.Spor.Raw

public section

namespace CFSG.KS.Raw

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def dupTabK (T : Nat) : Bool :=
  strictB (Nat.shiftRight (stCnt T) (nat_lit 1)) (fun q => bAnd(Nat.beq (stCnt T) (Nat.add q q),
    allN q (fun j => Nat.beq (stAt T (Nat.add q j)) (stAt T j))))

end CFSG.KS.Raw

end
