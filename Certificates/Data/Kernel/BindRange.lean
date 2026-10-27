module

public import Certificates.Data.Kernel.HOrb

public section

namespace CFSG.Certificates.BindS

open CFSG.KC CFSG.KC.LceS CFSG.Certificates.HO

@[expose] noncomputable def relsLet (RT : Nat → Nat) (nR : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun r ih => andB ih
    (andB (Nat.blt (wLen (RT r)) (nat_lit 256)) (lettersBelow (wWord (RT r)) (wLen (RT r)) (nat_lit 254)))) nR

end CFSG.Certificates.BindS

end
