module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyA11NbrOn
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenKGDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGLabC3D4Seven (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab = ⟨.C, 3, 3⟩ ∨ lab = ⟨.twD, 4, 3⟩) ∧ p = 7

@[expose] def GGCorFiveTwentyA11RootGenC3D4Input : Prop :=
  GGCorFiveTwentyA11CfgRootGenNbrInputOn GGLabC3D4Seven

end CFSG.StandardType

end
