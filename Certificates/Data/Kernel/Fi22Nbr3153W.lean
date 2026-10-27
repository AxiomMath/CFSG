module

public import Certificates.Data.Kernel.Fi22Nbr3153

public section

namespace CFSG.KC.N3153

open CFSG.KC.Enum

@[expose] noncomputable def roundK (H s x : Nat) : Nat :=
  strictN (Nat.land x H) fun a => Nat.lor (Nat.xor x a) (Nat.shiftLeft a s)

@[expose] noncomputable def rowOKW (n d : Nat) (R M S : Nat → Nat) (D : Nat → Nat) (x : Nat) :
    Bool :=
  strictB (R x) fun r => strictB (M x) fun m =>
    bAnd(Nat.blt (rg r (Nat.sub d (nat_lit 1))) n,
    bAnd(allN (Nat.sub d (nat_lit 1)) (fun i => Nat.blt (rg r i) (rg r (Nat.add i (nat_lit 1)))),
    bAnd(Nat.beq (Nat.shiftRight (maskK d r) (nat_lit 64)) m,
    bAnd(Nat.blt m (Nat.shiftLeft (nat_lit 1) (nat_lit 4096)),
      Nat.beq (S x) (Nat.add (Nat.add x (nat_lit 1)) (Nat.shiftLeft (D m) (nat_lit 128)))))))

end CFSG.KC.N3153

end
