module

public import Certificates.Data.Kernel.Fi22Nbr3153

public section

namespace CFSG.KC.N3153

open CFSG.KC.Enum

@[expose] noncomputable def imgOKM (n d g : Nat) (R M : Nat → Nat) (x : Nat) : Bool :=
  strictB (pg (nat_lit 12) (nat_lit 4095) g x) fun y =>
    bAnd(Nat.blt y n, strictB (R x) fun r => strictB (M y) fun m =>
      allN d (fun i => Nat.beq (Nat.land (Nat.shiftRight m
        (pg (nat_lit 12) (nat_lit 4095) g (rg r i))) (nat_lit 1)) (nat_lit 1)))

@[expose] noncomputable def sortK16 (k r : Nat) : Bool :=
  strictB (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 16) k)) fun P =>
  strictB (Nat.div (Nat.sub P (nat_lit 1)) (nat_lit 65535)) fun o =>
  strictB (Nat.mul (nat_lit 32768) o) fun g =>
    Nat.beq (Nat.land (Nat.sub (Nat.add g (Nat.mod (Nat.shiftRight r (nat_lit 16)) P))
      (Nat.add (Nat.mod r P) o)) g) g

@[expose] noncomputable def rowOKP (n d : Nat) (R M S : Nat → Nat) (D : Nat → Nat) (x : Nat) :
    Bool :=
  strictB (R x) fun r => strictB (M x) fun m => strictB (D m) fun s =>
    bAnd(Nat.blt (rg r (Nat.sub d (nat_lit 1))) n,
    bAnd(sortK16 (Nat.sub d (nat_lit 1)) r,
    bAnd(allN d (fun i => Nat.beq (Nat.land (Nat.shiftRight m (rg r i)) (nat_lit 1)) (nat_lit 1)),
    bAnd(Nat.blt m (Nat.shiftLeft (nat_lit 1) (nat_lit 4096)),
    bAnd(Nat.beq (Nat.mod s (nat_lit 281474976710655)) d,
      Nat.beq (S x) (Nat.add (Nat.add x (nat_lit 1)) (Nat.shiftLeft s (nat_lit 128))))))))

end CFSG.KC.N3153

end
