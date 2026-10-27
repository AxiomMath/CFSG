module

public import CFSG.Milestones.ASVolI.F48.Small.U42eInputs
import Certificates.Kernel.F48Small.U42eGlue

public section

open CFSG CFSG.ASVolI

namespace Certificates

open CertificateChecks

open CFSG CFSG.ASVolI in
theorem certificate7553 : burnsideF48s_u42eCheckGens () = true ∧
    burnsideF48s_u42eCheckRels () = true ∧
    burnsideF48s_u42eCheckLetters () = true :=
  ⟨KernelF48S.gens_ok, KernelF48S.rels_ok, KernelF48S.checkLetters⟩

end Certificates
