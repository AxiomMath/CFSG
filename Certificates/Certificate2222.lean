module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.Blueprint.NativeSporadic
import CFSG.Sporadic.SmallOddCore.HSAut

public section

namespace Certificates

theorem certificate2222 : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
    CFSG.Blueprint.NativeSporadic.HS) ≤ 2 :=
  CFSG.Sporadic.Schreier.outer_card_le_of_equiv CFSG.Sporadic.SmallOddCore.hs_outer_card_le
    CFSG.Sporadic.Schreier.hsPermEquiv

end Certificates
