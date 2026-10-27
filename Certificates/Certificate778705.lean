module

public import CFSG.CGT.Stroth77.NonSplitCore.CertInputs
import CFSG.Certificates.Kernel.Stroth77.NonSplitSound
import Certificates.Kernel.Stroth77.NonSplitChecks

public section

namespace Certificates

open CFSG.KC.Stroth77NS CFSG.KD.Stroth77NS

open CFSG.CGT.Stroth77.Core in
theorem certificate778705 : (∀ j, evalW sw (rel j) = 1)
    ∧ (∀ i, ∀ e ∈ ((cycles i).map fun c => (vtx c.1, rel c.2)).flatMap
    (fun c => walk sw c.1 c.2), Even ((((cycles i).map fun c => (vtx c.1, rel c.2)).flatMap
      (fun c => walk sw c.1 c.2)).count e))
    ∧ (certLHS = certRHS) :=
  ⟨ch778705_rel, cycles_even_k ch778705_cyc,
    certLHS_eq_certRHS_k ch778705_g ch778705_tits ch778705_cert⟩

end Certificates
