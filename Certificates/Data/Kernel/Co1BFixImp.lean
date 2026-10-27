module

public import Certificates.Data.Kernel.M1F2
public import CFSG.Certificates.Kernel.Enum.Defs
public import Certificates.Data.Kernel.Spor.Chain
public import CFSG.Certificates.Kernel.Lie.CT.Core

public section

namespace CFSG.KC.Co1B

open CFSG.KC.M1F2 CFSG.KC.Enum CFSG.KLie.CT

@[expose] noncomputable def fixAllT (TQ : List Nat) (v : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun t _ ih => andB (Nat.beq (vmF (nat_lit 24) t v) v) ih) TQ

@[expose] noncomputable def fixImpChunkK (T : Nat) (TQ : List Nat) (P : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun k acc => andB ((fun v => Bool.rec (motive := fun _ => Bool) true (fixAllT TQ v)
      (Nat.beq (vmF (nat_lit 24) T v) v)) (pg (nat_lit 24) (CFSG.KS.mask (nat_lit 24)) P k)) acc)
    (nat_lit 840)

@[expose] noncomputable def fixImpTabK (T : Nat) (TQ : List Nat) (F : Nat → Nat) (m : Nat) :
    Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun j acc => andB (fixImpChunkK T TQ (F j)) acc) m

end CFSG.KC.Co1B

end
