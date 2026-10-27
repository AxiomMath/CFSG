module

public import Certificates.Data.Kernel.Spor.Fi24PumpK

public section

namespace CFSG.KC.Fi24Ctl3

open CFSG.KC.Fi24PumpK

@[expose] noncomputable def ctlOK (E : List Nat → List Nat → Bool) (r g x y h : List Nat) : Bool :=
  letLt r && letLt g && letLt x && letLt y && letLt h && E (r ++ r ++ r) [] &&
    E (r ++ g) (g ++ x) && E (x ++ [2]) ([2] ++ x) && E (x ++ y) (y ++ x) &&
    E (x ++ h) (h ++ y) && (E (y ++ [0]) ([0] ++ y) || E h [0])

end CFSG.KC.Fi24Ctl3

end
