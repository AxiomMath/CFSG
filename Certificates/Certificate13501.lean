module

public import CFSG.HardMathSupport.Solomon.Coordinator.I10_21Fi22Inputs
import CFSG.Certificates.Kernel.OpsLayElem2Sound
import Certificates.Kernel.OpsLaySigned.Fi22Elem2

public section

open CertificateChecks.KernelFusLay CFSG.HardMathSupport.Solomon.Coordinator CFSG.KC.OpsLayK

namespace Certificates

open CertificateChecks

theorem certificate13501 : CFSG.HardMathSupport.Solomon.Coordinator.i1021Fi22Check = true := by
  have hA := Snd.rel_decode Fi22.lay_ok rfl Fi22.decA Fi22.LA_eq
  have h := CFSG.KC.OpsLayElem2.elem2K_sound (d := 77) (X := i1021Fi22RegA)
    (Y := i1021Fi22RegB) Fi22.lay_ok rfl rfl hA hA
    (Snd.rel_decode Fi22.lay_ok rfl Fi22.decB Fi22.LB_eq) rfl
    KernelOpsLaySigned.Fi22.elem13501_K
  rw [List.map_ofFn] at h
  exact h

end Certificates
