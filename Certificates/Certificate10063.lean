module

public import CFSG.Sporadic.Co1.Cover.Data
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import Certificates.Kernel.Co1Cover.Bridge

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Co1.CoverNative CFSG.Sporadic.Co1.Cover CFSG.Sporadic.Co1.InvNative
  CFSG.Sporadic.SmallF2.Native in
theorem certificate10063 :
    (relCheckAB 24 (rrCov 4) (rrCov 5) (invRows (rrCov 4)) (invRows (rrCov 5))
      TauCeti.SporadicName.M24.presentation.relatorLetters = true)
    ∧ (relCheckAB 11 Aa Ba Aa (mulRows 11 Ba Ba)
      TauCeti.SporadicName.M24.presentation.relatorLetters = true)
    ∧ (CFSG.Sporadic.SmallF2.rowsMatrix 24 (mulRows 24 (rrCov 4) (rrCov 5)) ≠
      CFSG.Sporadic.SmallF2.rowsMatrix 24 (mulRows 24 (rrCov 5) (rrCov 4))) := KernelCo1Cover.facts10063

end Certificates
