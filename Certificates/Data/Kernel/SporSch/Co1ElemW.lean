module

public import Certificates.Data.Kernel.SporSch.Co1Elem
public import Certificates.Data.Kernel.Co1BW

public section

namespace CFSG.KS.SporSch.M24

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def powEW (X e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) idM (fun _ ih => strictN ih (fun Y => CFSG.KC.Co1B.mulWK Y X)) e

@[expose] noncomputable def eProdW (A : Nat → Nat) (n : Nat) : Nat :=
  foldN (nat_lit 6) (fun i acc => CFSG.KC.Co1B.mulWK (powEW (A i) (dig3 n i)) acc) idM

@[expose] noncomputable def incSlW (A : Nat → Nat) (MsP lo len : Nat) : Bool :=
  allN len (fun d => strictB (Nat.add lo d) (fun k => bIf(Nat.blt (Nat.succ k) (nat_lit 729),
    Nat.blt (eProdW A (idxK MsP k)) (eProdW A (idxK MsP (Nat.succ k))), true)))

@[expose] noncomputable def eChkW (A : Nat → Nat) (MsP : Nat) : Bool :=
  bAnd(distP MsP (nat_lit 729) (nat_lit 0),
    allN (nat_lit 6) (fun i => Nat.beq (eProdW A (Nat.pow (nat_lit 3) i)) (A i)))

end CFSG.KS.SporSch.M24

end
