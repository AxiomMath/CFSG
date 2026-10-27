module

public import Certificates.Data.Kernel.LocalQT.Lat
public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.LQT.L

@[expose] noncomputable def mul7 (n s t : Nat) : Nat :=
  CFSG.KC.Enum.pcomp n (nat_lit 7) (nat_lit 127) s t

@[expose] noncomputable def one7 (n : Nat) : Nat := CFSG.KC.Enum.pidn n (nat_lit 7)

@[expose] noncomputable def bfsK7 (n : Nat) (G : List Nat) (d : Nat) : SetK :=
  bfsG (mul7 n) (one7 n) G d

@[expose] noncomputable def closedK7 (n : Nat) (G : List Nat) (S : SetK) : Bool :=
  closedG (mul7 n) (one7 n) G S

end CFSG.KC.LQT.L

end
