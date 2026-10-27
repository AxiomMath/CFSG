module

public import Certificates.Data.Kernel.MonsterB.Orb14
public import Certificates.Data.Kernel.F4Mat

public section

namespace CFSG.KC.U6G

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.F4M CFSG.KC.Orb14

@[expose] noncomputable def cv (x t : Nat) : Nat := fget x t (nat_lit 2)

@[expose] noncomputable def mkV (f : Nat → Nat) : Nat :=
  orN (nat_lit 6) fun t => Nat.shiftLeft (Nat.land (f t) (nat_lit 3)) (Nat.mul (nat_lit 2) t)

@[expose] noncomputable def hUK (x y : Nat) : Nat :=
  xorN (nat_lit 3) fun i => Nat.xor (fm (cv x i) (sqC (cv y (Nat.add i (nat_lit 3)))))
    (fm (cv x (Nat.add i (nat_lit 3))) (sqC (cv y i)))

@[expose] noncomputable def barc (f : Bool) (c : Nat) : Nat := nIf(f, sqC c, c)

@[expose] noncomputable def imK (f : Bool) (M : Nat → Nat) (x : Nat) : Nat :=
  strictN x fun x => mkV fun t => xorN (nat_lit 6) fun r => fm (barc f (cv x r)) (cv (M r) t)

@[expose] noncomputable def expK (R : Nat → Nat) (x : Nat) : Nat :=
  strictN x fun x => mkV fun t => xorN (nat_lit 3) fun b => fm (cv x (pivK (R b))) (cv (R b) t)

@[expose] noncomputable def gramOK (M : Nat → Nat) : Bool :=
  allN (nat_lit 6) fun i => allN (nat_lit 6) fun j => Nat.beq (hUK (M i) (M j))
    (nIf(Nat.beq j (Nat.mod (Nat.add i (nat_lit 3)) (nat_lit 6)), nat_lit 1, nat_lit 0))

end CFSG.KC.U6G

end
