module

public import Certificates.Data.E64Facts
import Certificates.Kernel.E64FactsK.Glue

public section

namespace Certificates

open Certificates.E64Facts in
theorem certificate550841 : g1Check () = true ∧ g2Check () = true ∧ Certificates.E64Facts.conjCheck () = true :=
  ⟨CFSG.KD.E64FactsK.g1Check_k, CFSG.KD.E64FactsK.g2Check_k, CFSG.KD.E64FactsK.conjCheck_k⟩

end Certificates
