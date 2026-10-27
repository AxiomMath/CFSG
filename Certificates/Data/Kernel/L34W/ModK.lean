module

public import Certificates.Data.Kernel.L34W.Outer

public section

namespace CFSG.KC.L34W

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def bitC (m l : Nat) : Bool :=
  Nat.beq (Nat.mod (Nat.shiftRight m l) (nat_lit 2)) (nat_lit 1)

@[expose] noncomputable def eqC (m x y : Nat) : Bool :=
  bAnd(Nat.beq (Nat.div x (nat_lit 16)) (Nat.div y (nat_lit 16)),
    bitC m (Nat.add
      (Nat.mul (nat_lit 4) (Nat.mod (Nat.sub (Nat.add (Nat.mod (Nat.div x (nat_lit 4)) (nat_lit 4)) (nat_lit 4))
        (Nat.mod (Nat.div y (nat_lit 4)) (nat_lit 4))) (nat_lit 4)))
      (Nat.mod (Nat.sub (Nat.add (Nat.mod x (nat_lit 4)) (nat_lit 4)) (Nat.mod y (nat_lit 4))) (nat_lit 4))))

@[expose] noncomputable def isInvC (T : Nat → Nat) (m x : Nat) : Bool :=
  bAnd(eqC m (mulC T x x) (nat_lit 0), bNot (eqC m x (nat_lit 0)))

@[expose] noncomputable def commC (T : Nat → Nat) (m x y : Nat) : Bool :=
  eqC m (mulC T x y) (mulC T y x)

@[expose] noncomputable def twoC (T : Nat → Nat) (m a b c d : Nat) : Bool :=
  bAnd(bAnd(bAnd(Nat.blt a (nat_lit 1024), Nat.blt b (nat_lit 1024)),
      bAnd(Nat.blt c (nat_lit 1024), Nat.blt d (nat_lit 1024))),
    bAnd(bAnd(bAnd(isInvC T m a, isInvC T m b), bAnd(isInvC T m c, isInvC T m d)),
      bAnd(bAnd(bNot (eqC m b a), commC T m a b),
        bAnd(bAnd(commC T m c a, commC T m c b),
          bAnd(bAnd(commC T m d a, commC T m d b), bNot (commC T m c d))))))

end CFSG.KC.L34W

end
