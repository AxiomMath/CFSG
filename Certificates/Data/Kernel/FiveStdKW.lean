module

public import Certificates.Data.Kernel.FiveStdKN

public section

namespace CFSG.KC.FiveStdK

@[expose] noncomputable def p2K (K1 : List Nat) (g2 : Nat) : List Nat :=
  (powersK g2 5).flatMap fun x => K1.map fun k => mulK x k

@[expose] noncomputable def cenSubK (P : List Nat) (B M d di : Nat) : Bool :=
  allN M fun j => memL P (cjK d di (f20 B j))

@[expose] noncomputable def cenSupK (P : List Nat) (g2 : Nat) : Bool :=
  allL P fun y => andB (validK y) (Nat.beq (mulK y g2) (mulK g2 y))

end CFSG.KC.FiveStdK

end
