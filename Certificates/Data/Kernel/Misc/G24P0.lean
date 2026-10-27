module

public import Certificates.Data.Kernel.Misc.G24

public section

namespace CFSG.KC.Misc.G24

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc

@[expose] noncomputable def g24P0K (Gb p1 p2 zx zy : List Nat) : Bool :=
  letB (wordF4 Gb (parseK p1)) fun P1 => letB (wordF4 Gb (parseK p2)) fun P2 =>
  letB (wordF4 Gb (appN (parseK zx) (parseK zy))) fun Z => letB (oneF2 28) fun I =>
  letB (mulF2 28 P1 P1) fun Q1 => letB (mulF2 28 P2 P2) fun Q2 =>
  andB (Nat.beq (mulF2 28 P1 Q1) I) <| andB (Nat.beq (mulF2 28 P2 Q2) I) <|
  andB (Nat.beq (mulF2 28 (mulF2 28 (mulF2 28 P1 P2) Q1) Q2) Z) <|
  andB (Nat.beq (mulF2 28 Z P1) (mulF2 28 P1 Z)) <|
  andB (Nat.beq (mulF2 28 Z P2) (mulF2 28 P2 Z)) <|
  andB (andB (Nat.blt Z (Nat.shiftLeft 1 784)) (Nat.blt I (Nat.shiftLeft 1 784)))
    (notB (Nat.beq Z I))

end CFSG.KC.Misc.G24

end
