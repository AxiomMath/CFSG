module

public import Certificates.Data.Kernel.B45Perm.RuSyl
public import Certificates.Data.Kernel.InvTabK

public section

namespace CFSG.KC.B45P.RuSyl

open CFSG.KC.InvTabK

@[expose] def quadC (WQ : Nat → Nat) (k t : Nat) : Nat := fld(WQ k, Nat.mul 9 t, 511)

@[expose] def witC (WQ : Nat → Nat) (nw : Nat) (S : List Nat) : Bool :=
  (List.range nw).any fun k => (List.range 4).all fun t => S.contains (quadC WQ k t)

@[expose] def predC (CM PR WQ : Nat → Nat) (nw : Nat) (l : List Nat) : Bool :=
  witC WQ nw (subprodsF 495 (pK PR) l) && forallGreedyF 495 (cK CM) (pK PR) (fun _ => false) 2 l

@[expose] def rootC (CM PR WQ : Nat → Nat) (nw r : Nat) : Bool :=
  forallGreedyF 495 (cK CM) (pK PR) (predC CM PR WQ nw) 4 [r]

end CFSG.KC.B45P.RuSyl

end
