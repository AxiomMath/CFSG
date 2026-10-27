module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisFusCertInputs
public import Mathlib.Tactic.Ring

public section

open CFSG.ComponentClassification.GHarris.SCert

namespace CFSG.KC.GHFus

@[expose] def clsWOK (W : List (Nat × Nat)) : Bool :=
  W.all fun p => decide (SE.clsTab (SE.dec p.1) < 9) &&
    (SE.dec p.2)⁻¹ * SE.dec p.1 * SE.dec p.2 == SE.invRep (Fin.ofNat 9 (SE.clsTab (SE.dec p.1)))

@[expose] def clsCover (W : List (Nat × Nat)) : Bool :=
  SE.allList.all fun s => !(SE.isInvB s) || W.any fun p => p.1 == s.enc

end CFSG.KC.GHFus
