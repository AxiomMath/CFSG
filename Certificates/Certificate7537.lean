module

public import CFSG.Milestones.ASVolI.F48.Small.Sp43Inputs
import Certificates.Kernel.F48Small.Sp43Glue

public section

open CFSG CFSG.ASVolI

namespace Certificates

open CertificateChecks

open CFSG CFSG.ASVolI in
theorem certificate7537 : burnsideF48s_sp43CheckGens () = true ∧ burnsideF48s_sp43CheckRels () = true ∧
    burnsideF48s_sp43CheckLetters () = true ∧ burnsideF48s_sp43CheckClosed () = true ∧
    burnsideF48s_sp43CheckCand () = true :=
  ⟨KernelF48S.gensSp43_ok, KernelF48S.relsSp43_ok, KernelF48S.sp43_checkLetters,
    KernelF48S.sp43_checkClosed, KernelF48S.sp43_checkCand⟩

end Certificates
