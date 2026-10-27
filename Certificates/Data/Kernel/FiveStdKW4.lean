module

public import Certificates.Data.Kernel.FiveStdKW3

public section

namespace CFSG.KC.FiveStdK

@[expose] noncomputable def eqLK (L M : List Nat) : Bool :=
  (L.all fun x => M.contains x) && M.all fun x => L.contains x

@[expose] noncomputable def hInvK (a b g g2 h : Nat) : Bool :=
  Nat.beq h oneK || !(normAllK [a, b] [h] (powersK h 5)) || eqLK (powersK h 5) (powersK g 5) ||
    eqLK (powersK h 5) (powersK g2 5)

@[expose] noncomputable def gRestK (t u a b g : Nat) : Bool :=
  letB (cjK t (invK t) g) fun g2 =>
    normAllK [a, b] [g] (powersK g 5) && Nat.beq (cjK u (invK u) g) (invK g) &&
    Nat.beq (mulK g g2) (mulK g2 g) && decide (ppK g g2 5 5).Nodup &&
    (ppK g g2 5 5).all (hInvK a b g g2) &&
    ((ppK g g2 5 5).filter fun x => Nat.beq (mulK x t) (mulK t x)).length == 5

end CFSG.KC.FiveStdK

end
