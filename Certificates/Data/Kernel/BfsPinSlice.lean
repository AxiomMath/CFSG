module

public import Certificates.Data.Kernel.BfsPin

public section

namespace CFSG.KC.BfsPin

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw

@[expose] noncomputable def runF (n w m ng : Nat) (G T E : Nat → Nat) (len : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ c => c)
    (fun _ ih lo c => strictN (nIf(Nat.blt lo c, pointStep n w m ng G T E lo c, nat_lit 0))
      (ih (Nat.succ lo))) len

@[expose] noncomputable def runSl (n w ng : Nat) (G T E : Nat → Nat) (L : Nat) (C : Nat → Nat)
    (s : Nat) : Bool :=
  Nat.beq (runF n w (mask w) ng G T E L (Nat.mul L s) (C s)) (C (Nat.succ s))

@[expose] noncomputable def canonSl (n w : Nat) (T : Nat → Nat) (L s : Nat) : Bool :=
  allN L fun i => canonK n w (mask w) (Nat.mul n w) (T (Nat.add (Nat.mul L s) i))

end CFSG.KC.BfsPin

end
