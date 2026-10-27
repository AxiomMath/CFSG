module

public import Certificates.Certificate589301

public section

namespace CFSG.Quasithin.KGC31.J4M4.Gen

open CFSG.Sporadic.J4 CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.J4

theorem chkGen_facts :
    z1Elt * z1Elt = 1 ∧ cElt ^ 11 = 1 ∧ cElt * z1Elt = z1Elt * cElt ∧
      uElt * z1Elt * uElt⁻¹ = fJ 9 ∧
      ∃ gM : GL (Fin 112) (ZMod 2),
        ((apElt : G₀) : GL (Fin 112) (ZMod 2)) * gM = gM * gA ∧
          ((bpElt : G₀) : GL (Fin 112) (ZMod 2)) * gM = gM * gB :=
  Certificates.certificate589301

end CFSG.Quasithin.KGC31.J4M4.Gen

end
