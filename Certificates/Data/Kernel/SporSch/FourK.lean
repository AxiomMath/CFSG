module

public import Certificates.Data.Kernel.Spor.Raw

public section

namespace CFSG.KS.SporSch.FourK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def commCntK (n w cnt : Nat) (T : Nat → Nat) (x : Nat) : Nat :=
  (List.range cnt).countP fun k =>
    Nat.beq (pcomp n w (mask w) (T k) x) (pcomp n w (mask w) x (T k))

@[expose] noncomputable def fourAt (n w cnt : Nat) (T : Nat → Nat) (A bound j : Nat) : Bool :=
  strictB (T j) fun x =>
    !Nat.beq (pcomp n w (mask w) x x) (pidn n w) || Nat.beq x (pidn n w) || Nat.beq x A ||
      Nat.beq (bound % commCntK n w cnt T x) 0

end CFSG.KS.SporSch.FourK

end
