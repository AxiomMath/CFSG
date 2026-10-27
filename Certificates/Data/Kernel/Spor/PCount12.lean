module

public import Certificates.Data.Kernel.Spor.PCount

public section

namespace CFSG.KS.PCnt

open CFSG.KC.Enum

@[expose] noncomputable def ordTwelve (n w m I c : Nat) : Nat :=
  strictN (pcomp n w m c c) fun x2 => strictN (pcomp n w m x2 x2) fun x4 =>
    strictN (pcomp n w m x4 x2) fun x6 =>
      nIf(Nat.beq (pcomp n w m x6 x6) I,
        nIf(Nat.beq x4 I, nat_lit 0, nIf(Nat.beq x6 I, nat_lit 0, nat_lit 1)), nat_lit 0)

end CFSG.KS.PCnt

end
