module

public import Certificates.Data.Kernel.FrameE78K

public section

namespace CFSG.KC.FrameWhole

open CFSG.KC.Enum CFSG.KC.FrameE78

@[expose] noncomputable def fullM (m : Nat) : Nat := Nat.sub (Nat.pow (nat_lit 2) m) (nat_lit 1)

@[expose] noncomputable def connK (n m RP LV : Nat) : Bool :=
  allN m fun a => orB (Nat.beq a (nat_lit 0)) (strictB (vget LV a) fun l =>
    notB (allN m fun p => notB (bAnd(Nat.blt (vget LV p) l,
      notB (Nat.beq (bf n RP p a) (nat_lit 0))))))

end CFSG.KC.FrameWhole

end
