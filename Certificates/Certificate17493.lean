module

public import CFSG.YGroups.Y443.Native.EdgeNoncommInputs
public import Certificates.Data.TabMSevenHe
import Certificates.Kernel.KDenseP.HeSeven

public section

namespace Certificates

open CertificateChecks

open CFSG.YGroups.Y443 CFSG.YGroups.Y443Native CFSG.HardMathSupport.Dickson.I271.TabMSeven in
theorem certificate17493 :
    (fixAll (heChunk [6, 7, 9, 12]) (wV ()) = true)
    ∧ (EdgeNoncomm.moveCheck heA (CFSG.YGroups.Y443Native.bV ()) = true) :=
  ⟨(KernelKDenseP.HeSeven.fixAll_heChunk (by decide)).2.2, KernelKDenseP.HeSeven.moveCheck_heA_b⟩

end Certificates
