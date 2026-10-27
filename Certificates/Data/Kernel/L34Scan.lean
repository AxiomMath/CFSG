module

public import Certificates.Data.Kernel.L34K

public section

namespace CFSG.KC.L34Scan

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K
open CFSG.KLie.CT (andB orB notB)

@[expose] noncomputable def pow2K (n w k x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) x (fun _ y => pcomp n w (mask w) y y) k

@[expose] noncomputable def fixK (n w r CN : Nat) (CP : Nat → Nat) (e x : Nat) : Bool :=
  orB (notB (commPt n w x r)) (orB (notB (allN CN fun c => commPt n w x (CP c)))
    (orB (notB (Nat.beq (pow2K n w (nat_lit 8) x) e)) (orB (Nat.beq x e) (Nat.beq x r))))

@[expose] noncomputable def twoK (n w CN : Nat) (CP : Nat → Nat) (e x : Nat) : Bool :=
  orB (notB (allN CN fun c => commPt n w x (CP c))) (Nat.beq (pow2K n w (nat_lit 8) x) e)

@[expose] noncomputable def scanSl (f : Nat → Bool) (T : Nat → Nat) (L s : Nat) : Bool :=
  allN L fun i => strictB (T (Nat.add (Nat.mul L s) i)) f

end CFSG.KC.L34Scan

end
