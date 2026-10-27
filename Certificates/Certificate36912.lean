module

public import Certificates.Kernel.Sporadic.Fi24Pump.Glue
import Certificates.Kernel.Sporadic.Fi24OrbL.Facts

public section

namespace Certificates

open CertificateChecks

theorem certificate36912_of_bridge
    (hL : ∀ l < 26, ∀ p < 306936,
      CFSG.Sporadic.Th.idx 306936 (CFSG.Perm.pairG CFSG.Sporadic.Fi24.gs l) p =
        CFSG.KS.Fi24Net.LN CFSG.KD.Fi24Net.NW l p) :
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three.Fi24PumpFacts :=
  by
    exact CFSG.KD.Fi24Pump.fi24PumpFacts_of_letters hL

theorem certificate36912 : 
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three.Fi24PumpFacts :=
  certificate36912_of_bridge KernelFi24OrbL.pairG_LN

end Certificates
