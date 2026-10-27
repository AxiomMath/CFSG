module

public import Certificates.Data.Kernel.Fi22Twist.Search

public section

namespace CFSG.KC.Fi22Twist

open CFSG.KC.Enum

@[expose] noncomputable def ctK (G T : Nat) : Bool :=
  allN (nat_lit 3510) (fun i => Nat.beq (ap G (ap T i)) (ap T (ap G i)))

end CFSG.KC.Fi22Twist

end
