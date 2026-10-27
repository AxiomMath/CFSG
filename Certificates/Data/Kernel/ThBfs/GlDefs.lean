module

public import Certificates.Data.Kernel.ThBfs.Defs

public section

namespace CFSG.KC.ThBfs

@[expose] noncomputable def glTab (k : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 0x6745cdef98ba3210) (nat_lit 0xf6e7a3b2d4c58190)
    (Nat.beq k (nat_lit 1))

@[expose] noncomputable def glImg (k c : Nat) : Nat :=
  Nat.mod (Nat.shiftRight (glTab k) (Nat.mul (nat_lit 4) c)) (nat_lit 16)

@[expose] noncomputable def glAct (e k : Nat) : Nat :=
  Nat.add (glImg k (Nat.mod e (nat_lit 16)))
    (Nat.add (Nat.mul (nat_lit 16) (glImg k (Nat.mod (Nat.div e (nat_lit 16)) (nat_lit 16))))
      (Nat.add (Nat.mul (nat_lit 256) (glImg k (Nat.mod (Nat.div e (nat_lit 256)) (nat_lit 16))))
        (Nat.mul (nat_lit 4096) (glImg k (Nat.mod (Nat.div e (nat_lit 4096)) (nat_lit 16))))))

end CFSG.KC.ThBfs

end
