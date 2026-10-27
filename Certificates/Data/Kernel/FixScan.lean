module

public import Certificates.Data.Kernel.SporSch.Co1VOrb
public import Certificates.Data.Kernel.M1F2

public section

namespace CFSG.KC.FixScan

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KS.SporSch.VOrb

@[expose] noncomputable def allFixK (Ms : List Nat) (x : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun Mt _ ih => andB (Nat.beq (vmF (nat_lit 24) Mt x) x) ih) Ms

@[expose] noncomputable def fixScanK (T : Nat → Nat) (Ms : List Nat) (lo len : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun j ih acc => strictN (nIf(allFixK Ms (ptK T (Nat.add lo j)), Nat.succ acc, acc)) ih) len

end CFSG.KC.FixScan

end
