module

public import CFSG.Quasithin.Vol2.KGFactJ4M4GenElts
import Certificates.Kernel.J4Gen589301.Glue

public section

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.J4 CFSG.Quasithin.KGC31.J4 CFSG.Quasithin.KGC31.J4M4
  CFSG.Quasithin.KGC31.J4M4.Gen in
theorem certificate589301 :
    z1Elt * z1Elt = 1 ∧ cElt ^ 11 = 1 ∧ cElt * z1Elt = z1Elt * cElt ∧
      uElt * z1Elt * uElt⁻¹ = fJ 9 ∧
      ∃ gM : GL (Fin 112) (ZMod 2),
        ((apElt : G₀) : GL (Fin 112) (ZMod 2)) * gM = gM * gA ∧
          ((bpElt : G₀) : GL (Fin 112) (ZMod 2)) * gM = gM * gB := KernelJ4Gen.facts589301

end Certificates

end

end
