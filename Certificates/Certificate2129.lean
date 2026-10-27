module

public import CFSG.Sporadic.ONOddCore.SylowEightCheckInputs
public meta import CFSG.Sporadic.Schreier.ONCheckSmallAux
import Certificates.Kernel.Sporadic.OddCore.ON2129F

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.ONOddCore CFSG.ONSchreier CFSG.PSL3Four.Native in
theorem certificate2129 : enumOK 32 sqTabs sqEnum = true ∧ sqEnum.tabs.size = 64 ∧
    enumOK 32 omegaTabs omegaEnum = true ∧ omegaEnum.tabs.size = 8 ∧
    omegaEnum.tabs.all (fun a => omegaEnum.tabs.all fun b => comp 32 a b == comp 32 b a) =
      true ∧
    omegaEnum.tabs.all (fun a => comp 32 a a == idTab 32) = true := KernelSpor.ON2129.facts2129

end Certificates
