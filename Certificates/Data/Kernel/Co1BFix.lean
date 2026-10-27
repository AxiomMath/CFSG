module

public import Certificates.Data.Kernel.M1F2
public import CFSG.Certificates.Kernel.Enum.Defs
public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KC.Co1B

open CFSG.KC.M1F2 CFSG.KC.Enum

@[expose] noncomputable def fixChunkK (T P : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => (fun v => Bool.rec (motive := fun _ => Nat) acc (Nat.succ acc)
      (Nat.beq (vmF (nat_lit 24) T v) v)) (pg (nat_lit 24) (CFSG.KS.mask (nat_lit 24)) P k)) (nat_lit 840)

@[expose] noncomputable def fixTabK (T : Nat) (F : Nat → Nat) (m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun j acc => Nat.add (fixChunkK T (F j)) acc) m

end CFSG.KC.Co1B

end
