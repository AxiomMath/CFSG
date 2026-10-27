module

public import Certificates.Data.Kernel.LyOmega.Tree

public section

namespace CFSG.KC.LyOm

open CFSG.KC.Loop CFSG.KC.LL CFSG.KC.Ord

@[expose] noncomputable def canonM1 : Nat := rep1 (nat_lit 3) (nat_lit 49728)

@[expose] noncomputable def canon3 (x : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.land (Nat.shiftRight x (nat_lit 2)) (Nat.lor (Nat.shiftRight x (nat_lit 1)) x))
    canonM1) (nat_lit 0)

@[expose] noncomputable def canonRange (KX : Nat → Nat) (b₀ c : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun j ih => bAnd(canon3 (KX (Nat.add b₀ j)), ih)) c

end CFSG.KC.LyOm

end
