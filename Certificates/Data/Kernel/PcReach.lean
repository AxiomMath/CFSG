module

public import Certificates.Data.Kernel.LocalQT.PcW

public section

namespace CFSG.KC.PcReach

open CFSG.KC.Enum

@[expose] noncomputable def reachC (w m : Nat) (G : List Nat) (S : Nat) (recs : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun r _ ih S =>
      Nat.beq (Nat.land (Nat.shiftRight S (Nat.land (Nat.shiftRight r w) m)) 1) 1 &&
      Nat.beq (Nat.land (Nat.shiftRight S (Nat.land r m)) 1) 0 &&
      Nat.blt (Nat.shiftRight r (Nat.mul 2 w)) G.length &&
      Nat.beq (pg w m (G.getD (Nat.shiftRight r (Nat.mul 2 w)) 0) (Nat.land (Nat.shiftRight r w) m))
        (Nat.land r m) &&
      Nat.rec (motive := fun _ => Bool) (ih 0) (fun n _ => ih (Nat.succ n))
        (Nat.lor S (Nat.shiftLeft 1 (Nat.land r m))))
    recs S

end CFSG.KC.PcReach

end
