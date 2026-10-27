module

public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.Heisenberg
import Certificates.Kernel.SlpRelC.Fi22Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit in
theorem certificate129040 : ∃ (x y : Fin 3 → CFSG.Blueprint.NativeSporadic.Fi22)
    (z : CFSG.Blueprint.NativeSporadic.Fi22), HeisCfg 3 3 x y z ∧ ∀ i, y i ^ 3 = 1 := KernelSlpRel.fi22_heisCfg_exists

end Certificates
