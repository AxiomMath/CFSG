module

public import CFSG.Sporadic.HS.SmallF2Spec
public import Certificates.Data.CFSGNative.H13.J4Data
import Certificates.Kernel.H13J4.Img12

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.SmallF2 CFSG.Quasithin.H13.J4.Native in
theorem certificate7013 :
    rowsMatrix 12 uRows12 * rowsMatrix 12 uRows12 = 1 ∧
      rowsMatrix 12 vRows12 * (rowsMatrix 12 vRows12 * rowsMatrix 12 vRows12) = 1 ∧
      ∀ U V : Matrix.GeneralLinearGroup (Fin 12) (ZMod 2),
        (U : Matrix (Fin 12) (Fin 12) (ZMod 2)) = rowsMatrix 12 uRows12 →
        (V : Matrix (Fin 12) (Fin 12) (ZMod 2)) = rowsMatrix 12 vRows12 →
        2661120 ≤ Nat.card (Subgroup.closure
          ({U, V} : Set (Matrix.GeneralLinearGroup (Fin 12) (ZMod 2)))) := KernelH13.Img12.uv_facts

end Certificates
