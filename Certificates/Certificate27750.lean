module

public import CFSG.LocalAnalysis.EvenSporadicStandard.YS14.Fi24WitFacts
import Certificates.Kernel.Sporadic.Fi24F4.WFinal
public import CFSG.Sporadic.FischerOddCore.Fi24G2dFacts

public section

public section

namespace Certificates

open CFSG.EvenSporadicStandard.YS14 CFSG.Sporadic.FischerOddCore in
theorem certificate27750 : WitFacts (rep7 0) ∧ WitFacts (rep7 1) ∧ WitFacts (rep7 2) ∧
      WitFacts (rep7 5) ∧ WitFacts (rep7 6) := CFSG.KD.Fi24F4.witFacts_rep7

end Certificates

end

end
