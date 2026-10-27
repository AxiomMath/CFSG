module

public import Certificates.Data.Kernel.L34Norm

public section

namespace CFSG.KC.L34SelWord

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K
open CFSG.KLie.CT (fget andB orB notB anyN)

@[expose] noncomputable def selK (N : Nat) (J : Nat → Nat) (P : Nat → Bool) (M : Nat)
    (W : Nat → Nat) (ok : Nat → Nat → Bool) : Bool :=
  allN N fun q => strictB (J q) fun v =>
    orB (notB (P (Nat.mod v (nat_lit 32))))
      (anyN M fun m => andB (Nat.beq (fget (W m) (nat_lit 0) (nat_lit 32))
        (Nat.div v (nat_lit 32))) (ok m (Nat.div v (nat_lit 32))))

@[expose] noncomputable def wordK (n w c0 c1 : Nat) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun _ ih wd acc => strictN (pcomp n w (mask w) acc
        (nIf(Nat.beq (Nat.mod wd (nat_lit 2)) (nat_lit 0), c0, c1)))
      (ih (Nat.div wd (nat_lit 2))))

end CFSG.KC.L34SelWord

end
