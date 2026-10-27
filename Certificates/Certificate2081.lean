module

public import CFSG.Sporadic.GLQ.HNTwoRankInputs
import Certificates.Kernel.GLQ.HNTwoFacts

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.GLQ CFSG.Sporadic.GLQ.HNTwoRank CFSG.SectionRank in
open CFSG.SectionRank.Native CFSG.Blueprint Matrix in
theorem certificate2081 : ((opsP 5 133).eq
      ((opsP 5 133).pow ((opsP 5 133).decode NativeSporadic.HNSeed1) 2) (opsP 5 133).one = true
    )
    ∧ ((opsP 5 133).eq
      ((opsP 5 133).pow ((opsP 5 133).decode NativeSporadic.HNSeed2) 3) (opsP 5 133).one = true
    )
    ∧ (hnCheck = true) := KernelGLQ.HNTwo.facts2081

end Certificates
