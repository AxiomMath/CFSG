module

public import Certificates.Data.Kernel.Co1BW

public section

namespace CFSG.KC.Co1B

@[expose] noncomputable def strictB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def vAnyS (V : List Nat) (X Y : Nat) : Bool :=
  strictB X fun X => strictB Y fun Y => V.any fun v => eqK X (mulWK v Y)

@[expose] noncomputable def stabK (V : List Nat) (g X : Nat) : Bool := vAnyS V (mulWK g X) (mulWK X g)

@[expose] noncomputable def loopK (T V : List Nat) (A W g₁ g₂ x₁ rx ry : Nat) (vp : Bool) (r : Nat) :
    Bool :=
  (!T.all (fun t => eqK (mulWK r t) (mulWK t r)) || vp) &&
    (!vAnyS V (mulWK r x₁) (mulWK x₁ r) || vp) &&
    (!(stabK V g₁ r && stabK V g₂ r) ||
      ((!eqK (mulWK r r) A || V.any fun v => eqK r (mulWK v rx)) &&
        (!eqK (mulWK r r) W || V.any fun v => eqK r (mulWK v ry))))

@[expose] def isVP (c : Nat) (p : Nat × Nat) : Bool := c == 0 && (p.1 == 0 || p.1 == 1)

end CFSG.KC.Co1B

end
