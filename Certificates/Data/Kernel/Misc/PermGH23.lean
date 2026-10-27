module

public import Certificates.Data.Kernel.Misc.PermClos

public section

namespace CFSG.KC.Misc.GH23

@[expose] noncomputable def img8 (c i : Nat) : Nat :=
  Nat.mod (Nat.shiftRight c (Nat.mul (nat_lit 3) i)) (nat_lit 8)

@[expose] noncomputable def mul8 (a b : Nat) : Nat :=
  Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add
    (img8 a (img8 b (nat_lit 0)))
    (Nat.mul (nat_lit 8) (img8 a (img8 b (nat_lit 1)))))
    (Nat.mul (nat_lit 64) (img8 a (img8 b (nat_lit 2)))))
    (Nat.mul (nat_lit 512) (img8 a (img8 b (nat_lit 3)))))
    (Nat.mul (nat_lit 4096) (img8 a (img8 b (nat_lit 4)))))
    (Nat.mul (nat_lit 32768) (img8 a (img8 b (nat_lit 5)))))
    (Nat.mul (nat_lit 262144) (img8 a (img8 b (nat_lit 6)))))
    (Nat.mul (nat_lit 2097152) (img8 a (img8 b (nat_lit 7))))

@[expose] noncomputable def one8 : Nat := nat_lit 16434824

end CFSG.KC.Misc.GH23

end
