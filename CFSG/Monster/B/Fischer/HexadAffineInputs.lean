module

public import CFSG.Monster.B.Fischer.HexadDiag
public import CFSG.Monster.B.TwoA.Census.NatCert
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Certificates.Certificate3017
public import Certificates.Certificate3029
public meta import CFSG.Monster.B.Fischer.HexadDiag
public meta import CFSG.Monster.B.TwoA.Census.NatCert

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Fischer

open CFSG.Monster.Code CFSG.Monster.B.Classical.Mog22 CFSG.Monster.B.TwoA CFSG.Sporadic.Mathieu
  groupCohomology CFSG.Monster.B.TwoA.Census

variable {A A' : KB →* Equiv.Perm Q₀}

section Cocycle

variable {c : KB → Q₀}
  (hc : ∀ g h, c (g * h) = rhoQ g (c h) + c g)
include hc

end Cocycle

@[expose] def orbCert (twisted : Bool) (root : ℕ) : NatCert :=
  natBfs (fun k m => if twisted then alpha k m else linQ k m) 3 root 40

end CFSG.Monster.B.Fischer
