module

public import CFSG.Milestones.ASVolI.F48.Small.G2dInputs
import Certificates.Kernel.F48Small.G2dGlue

public section

open CFSG CFSG.ASVolI CFSG.Quasithin

namespace Certificates

open CertificateChecks

open CFSG CFSG.ASVolI CFSG.Quasithin in
theorem certificate7533 : burnsideF48s_g2dCheckGens () = true ∧ burnsideF48s_g2dCheckA () = true ∧
    burnsideF48s_g2dCheckB () = true ∧ burnsideF48s_g2dCheckCand () = true ∧
    burnsideF48s_g2dEvL (burnsideF48s_g2dCand 1) = List.range 28 ∧
    burnsideF48s_g2dEvL (burnsideF48s_g2dCand 3) = List.range 28 :=
  KernelF48S.certificate7533_facts

end Certificates
