module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeEnvelopePieces
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeNCNoSU3

public section

namespace CFSG.StandardType.RCKRP

theorem rckNoSmallB2_holds :
    RCKNoSmallB2 := by
  intro X _ _ t n f ψ p G₀ A B₁ D J L R Rm K e ht hcfg hKJ θ A' η E' S a i hfp hsmall
  exact (rckNC_two_lt_compRank ht hcfg hKJ hfp).ne' hsmall.2.1

end CFSG.StandardType.RCKRP

end
