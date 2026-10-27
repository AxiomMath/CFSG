module

public import Certificates.Data.Kernel.Spor.BTup

public section

namespace CFSG.KS.BTup

open CFSG.KC.Enum CFSG.KS.Row

@[expose] noncomputable def btEv (w m : Nat) (G : Nat → Nat) (e : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun p => p)
    (fun j ih p => strictN (ih p) (fun q =>
      nIf(Nat.beq (Nat.land (Nat.shiftRight e j) (nat_lit 1)) (nat_lit 1), pg w m (G j) q, q)))

@[expose] noncomputable def btNrK (w m d k : Nat) (G : Nat → Nat) (B N Y : Nat) : Bool :=
  Bool.not (allN (Nat.pow (nat_lit 2) k) (fun e => Bool.not (allN d (fun t =>
    Nat.beq (pg w m N (pg w m Y (pg w m B t))) (btEv w m G e k (pg w m N (pg w m B t)))))))

@[expose] noncomputable def btCjK (w m d kw km cnt : Nat) (K : Nat → Nat) (B C Y : Nat) : Bool :=
  Bool.not (allN cnt (fun q => Bool.not (strictB (btKey kw km K q) (fun x => allN d (fun t =>
    Nat.beq (pg w m C (pg w m x t)) (pg w m Y (pg w m C (pg w m B t))))))))

end CFSG.KS.BTup

end
