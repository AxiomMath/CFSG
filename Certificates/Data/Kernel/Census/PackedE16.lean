module

public import Certificates.Data.Kernel.Census.Packed

public section

namespace CFSG.KC.Census

section Checks

variable (n w : Nat)

@[expose] noncomputable def pisInv (a : Nat) : Bool :=
  Nat.beq (pc n w a a) (pid n w) && !(Nat.beq a (pid n w))

@[expose] noncomputable def pinSpan3 (u v x t : Nat) : Bool :=
  [pid n w, u, v, x, pc n w u v, pc n w u x, pc n w v x, pc n w u (pc n w v x)].any (Nat.beq t)

@[expose] noncomputable def pe16At (inS : Nat → Bool) (I : List Nat) (u : Nat) : Bool :=
  inS u || I.all fun v => !(pcommA n w u v) || Nat.beq v u ||
    I.all fun x => !(pcommA n w u x) || !(pcommA n w v x) || Nat.beq x u || Nat.beq x v ||
      Nat.beq x (pc n w u v) ||
      I.all fun t => !(pcommA n w t u) || !(pcommA n w t v) || !(pcommA n w t x) ||
        pinSpan3 n w u v x t

@[expose] noncomputable def pe16OK (inS : Nat → Bool) (I : List Nat) : Bool :=
  I.all (pe16At n w inS I)

end Checks

end CFSG.KC.Census
