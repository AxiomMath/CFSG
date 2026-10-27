module

public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.Heisenberg
import Certificates.Kernel.SlpRelC.ONGlue

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit in
theorem certificate129009 : ∃ x y z g : CFSG.Blueprint.NativeSporadic.ON,
    HeisCfg 7 1 (fun _ => x) (fun _ => y) z ∧ y ^ 7 = 1 ∧ g * z * g⁻¹ = z⁻¹ := KernelSlpRel.on_heisCfg_exists

end Certificates
