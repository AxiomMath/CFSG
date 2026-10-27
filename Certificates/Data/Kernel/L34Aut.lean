module

public import Certificates.Data.Kernel.L34FixPow

public section

namespace CFSG.KC.L34Aut

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.L34FixPow CFSG.KC.L34K
open CFSG.KLie.CT (andB orB notB)

@[expose] noncomputable def invBy (r x : Nat) : Bool :=
  allN 42 fun p => Nat.beq
    (pg 6 (mask 6) r (pg 6 (mask 6) x (pg 6 (mask 6) r (pg 6 (mask 6) x p)))) p

@[expose] noncomputable def cjP (d di y : Nat) : Nat :=
  pcomp 42 6 (mask 6) y (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) d y) di)

@[expose] noncomputable def witK (p m : Nat) (D DI : Nat → Nat) (y : Nat) : Bool :=
  orB (notB (allN m fun a => fixPow (cjP (D a) (DI a) y) p))
    (notB (allN m fun a => strictB (cjP (D a) (DI a) y) fun u => allN m fun b =>
      fixPow (pcomp 42 6 (mask 6) u (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) (D b) y) (DI b))) p))

@[expose] noncomputable def witP (p m : Nat) (D DI : Nat → Nat) (ex : Bool) (x : Nat) : Bool :=
  orB (notB (fixPow x p)) (orB ex (witK p m D DI x))

@[expose] noncomputable def witPt (e r m : Nat) (D DI : Nat → Nat) (ex : Bool) (x : Nat) : Bool :=
  orB (notB (invBy r x)) (orB (Nat.beq x e)
    (andB (witP 3 m D DI ex x) (andB (witP 5 m D DI ex x) (witP 7 m D DI ex x))))

@[expose] noncomputable def cenPt (a b l0 l1 l2 l3 l4 l5 x : Nat) : Bool :=
  orB (notB (andB (commPt 42 6 x a) (commPt 42 6 x b)))
    (orB (Nat.beq x l0) (orB (Nat.beq x l1) (orB (Nat.beq x l2)
      (orB (Nat.beq x l3) (orB (Nat.beq x l4) (Nat.beq x l5))))))

@[expose] noncomputable def expPt (x : Nat) : Bool := orB (fixPow x 3) (notB (fixPow x 27))

end CFSG.KC.L34Aut

end
