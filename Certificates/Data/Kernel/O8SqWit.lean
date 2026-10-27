module

public import Certificates.Data.Kernel.PCent

public section

namespace CFSG.KC.O8Sq

open CFSG.KC.Enum (pcomp pidn strictB)
open CFSG.KS (mask pinvS)

@[expose] noncomputable def pc9 (p q : Nat) : Nat := pcomp (nat_lit 360) (nat_lit 9) (mask 9) p q

@[expose] noncomputable def pi9 (p : Nat) : Nat := pinvS (nat_lit 360) (nat_lit 9) (mask 9) p

@[expose] noncomputable def witOneK (r h v : Nat) : Bool :=
  strictB (pc9 h (pc9 v (pi9 h))) (fun g => strictB (pc9 r r) (fun z =>
    strictB (pc9 r (pc9 g (pc9 r (pi9 g)))) (fun y =>
      Nat.beq (pc9 g z) (pc9 z g) && Nat.beq (pc9 y y) (pidn (nat_lit 360) (nat_lit 9)) &&
        !Nat.beq y (pidn (nat_lit 360) (nat_lit 9)) && !Nat.beq y z)))

end CFSG.KC.O8Sq

end
