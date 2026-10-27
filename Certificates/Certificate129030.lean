module

public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.Heisenberg
import Certificates.Kernel.SlpRelC.Fi23Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit in
theorem certificate129030 : ∃ (x y : Fin 4 → CFSG.Blueprint.NativeSporadic.Fi23)
    (z : CFSG.Blueprint.NativeSporadic.Fi23), HeisCfg 3 4 x y z ∧ ∀ i, y i ^ 3 = 1 := KernelSlpRel.fi23_heisCfg_exists

end Certificates
