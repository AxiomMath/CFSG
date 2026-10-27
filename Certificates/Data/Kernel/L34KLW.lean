module

public import Certificates.Data.Kernel.L34Norm

public section

namespace CFSG.KC.L34KLW

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34Norm
open CFSG.KLie.CT (andB orB notB anyN)

@[expose] noncomputable def o4Pt (n w x : Nat) : Bool :=
  allN n fun p => Nat.beq (pg w (mask w) x (pg w (mask w) x (pg w (mask w) x (pg w (mask w) x p))))
    p

@[expose] noncomputable def comm2Pt (n w x y : Nat) : Bool :=
  allN n fun p => Nat.beq (pg w (mask w) x (pg w (mask w) y (pg w (mask w) y p)))
    (pg w (mask w) y (pg w (mask w) y (pg w (mask w) x p)))

@[expose] noncomputable def invAPt (n w t a : Nat) : Bool :=
  allN n fun p => Nat.beq (pg w (mask w) t (pg w (mask w) a p))
    (pg w (mask w) a (pg w (mask w) a (pg w (mask w) t p)))

@[expose] noncomputable def c4Pt (n w a b x : Nat) : Bool :=
  orB (notB (andB (andB (commPt n w x a) (commPt n w x b)) (o4Pt n w x))) (invPt n w x)

@[expose] noncomputable def q4Pt (n w N : Nat) (P : Nat → Nat) (a b x y : Nat) : Bool :=
  andB (andB (inPts n w N P y a) (inPts n w N P y b))
    (andB (andB (o4Pt n w y) (notB (invPt n w y))) (comm2Pt n w x y))

@[expose] noncomputable def tauPt (n w e a b x t : Nat) : Bool :=
  andB (andB (invPt n w t) (notB (Nat.beq t e)))
    (andB (andB (invAPt n w t a) (invAPt n w t b)) (commPt n w x t))

@[expose] noncomputable def klEnt (n w N : Nat) (P : Nat → Nat) (e a b : Nat) (X : Nat → Nat)
    (M : Nat) (Q Y T : Nat → Nat) (q v : Nat) : Bool :=
  bIf(Nat.beq (Nat.mod v (nat_lit 2)) (nat_lit 1),
    strictB (X (Nat.div v (nat_lit 32))) fun x =>
      andB (c4Pt n w a b x)
        (bIf(Nat.beq (Nat.div (Nat.mod v (nat_lit 32)) (nat_lit 8)) (nat_lit 3),
          anyN M fun j => andB (Nat.beq (Q j) q)
            (andB (q4Pt n w N P a b x (Y j)) (tauPt n w e a b x (T j))),
          true)),
    true)

end CFSG.KC.L34KLW

end
