module

public import CFSG.Milestones.ASVolI.F48.Small.AutChartInputs
import Certificates.Kernel.AutChart.Sp43Glue

public section

open CFSG CFSG.ASVolI

namespace Certificates

open CertificateChecks

open CFSG CFSG.ASVolI in
theorem certificate7545 : burnsideF48s_autc_sp43_checkRel () = true ∧ burnsideF48s_autc_sp43_checkSub () = true ∧
    burnsideF48s_autc_sp43_checkInf () = true :=
  ⟨KernelAutChart.ch7545rel, KernelAutChart.checkSub_true, KernelAutChart.checkInf_true⟩

end Certificates
