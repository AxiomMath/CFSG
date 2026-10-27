module

public import CFSG.Milestones.ASVolI.F48.Small.Sp43ChartInputs
import Certificates.Kernel.F48Small.Sp43cGlue

public section

open CFSG CFSG.ASVolI

namespace Certificates

open CertificateChecks

open CFSG CFSG.ASVolI in
theorem certificate7538 : burnsideF48s_sp43c_checkGens () = true ∧ burnsideF48s_sp43c_checkSub () = true ∧
    burnsideF48s_sp43c_checkCover () = true ∧ burnsideF48s_sp43c_checkFar () = true ∧
    burnsideF48s_sp43c_checkXY () = true ∧ burnsideF48s_sp43c_checkS () = true ∧
    burnsideF48s_sp43c_checkNot () = true :=
  ⟨KernelF48S.gens43c_ok, KernelF48S.sp43c_checkSub, KernelF48S.sp43c_checkCover,
    KernelF48S.far43c_ok, KernelF48S.xy43c_ok, KernelF48S.sp43c_checkS,
    KernelF48S.sp43c_checkNot⟩

end Certificates
