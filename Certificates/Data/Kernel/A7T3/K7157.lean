module

public import Certificates.Data.Kernel.Misc.A7Nat

public section

namespace CFSG.KD.A7T3K

open CFSG.KC.LQT.P CFSG.KC.Ord CFSG.KD.A7Nat

@[expose] noncomputable def t0C : List Nat :=
  [6614517792, 6581914689, 6614450274, 6581978115, 6582009890, 6614418499, 6581946464,
    6614486017]

@[expose] noncomputable def smallK (L : List Nat) : Bool := andB (grpK L) (allL L (even 7))

@[expose] noncomputable def permT0K (L : List Nat) (s s2 : Nat) : Bool :=
  allL L fun t => letB (mul 7 t s) fun ts =>
    anyL L fun u => orB (Nat.beq ts u) (orB (Nat.beq ts (mul 7 s u)) (Nat.beq ts (mul 7 s2 u)))

@[expose] noncomputable def condK (L : List Nat) (s : Nat) : Bool :=
  letB (mul 7 s s) fun s2 => letB (mul 7 s s2) fun s3 =>
    impB (Nat.beq (mul 7 s3 (mul 7 s3 s3)) (one 7))
      (andB (Nat.beq s3 (one 7))
        (impB (permT0K L s s2) (anyL L fun t => Nat.beq (mul 7 t s) (mul 7 s2 t))))

@[expose] noncomputable def allK (L : List Nat) : Bool := allP 7 (condK L)

end CFSG.KD.A7T3K

end
