module

public import Certificates.Data.Kernel.Fi22Nbr3153W

public section

namespace CFSG.KC.N3153

open CFSG.KC.Enum

@[expose] noncomputable def rowSalt (x : Nat) : Nat :=
  Nat.land (Nat.mul (Nat.add x (nat_lit 1)) (nat_lit 11400714819323198485))
    (nat_lit 4611686018427387903)

@[expose] noncomputable def maskSK (d r c : Nat) : Nat :=
  foldN d (fun i a => Nat.add (Nat.lor a (Nat.shiftLeft (nat_lit 1) (Nat.add (nat_lit 64) (rg r i))))
    (nat_lit 1)) c

@[expose] noncomputable def imgMaskSK (d g r c : Nat) : Nat :=
  foldN d (fun i a => Nat.add (Nat.lor a (Nat.shiftLeft (nat_lit 1)
    (Nat.add (nat_lit 64) (pg (nat_lit 12) (nat_lit 4095) g (rg r i))))) (nat_lit 1)) c

@[expose] noncomputable def rowOKS (n d : Nat) (R M S : Nat → Nat) (D : Nat → Nat) (x : Nat) :
    Bool :=
  strictB (R x) fun r => strictB (M x) fun m =>
    bAnd(Nat.blt (rg r (Nat.sub d (nat_lit 1))) n,
    bAnd(allN (Nat.sub d (nat_lit 1)) (fun i => Nat.blt (rg r i) (rg r (Nat.add i (nat_lit 1)))),
    bAnd(Nat.beq (Nat.shiftRight (maskSK d r (rowSalt x)) (nat_lit 64)) m,
    bAnd(Nat.blt m (Nat.shiftLeft (nat_lit 1) (nat_lit 4096)),
      Nat.beq (S x) (Nat.add (Nat.add x (nat_lit 1)) (Nat.shiftLeft (D m) (nat_lit 128)))))))

@[expose] noncomputable def imgOKS (n d g : Nat) (R M : Nat → Nat) (x : Nat) : Bool :=
  strictB (pg (nat_lit 12) (nat_lit 4095) g x) fun y =>
    bAnd(Nat.blt y n, strictB (R x) fun r =>
      Nat.beq (Nat.shiftRight (imgMaskSK d g r (rowSalt x)) (nat_lit 64)) (M y))

end CFSG.KC.N3153

end
