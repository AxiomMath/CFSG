module

public import CFSG.YGroups.Y443.Native.Words
public import Certificates.Data.TabMSevenHe
import Certificates.Kernel.KDenseP.HeSeven

public section

namespace Certificates

open CertificateChecks

open CFSG.YGroups.Y443 CFSG.YGroups.Y443Native CFSG.HardMathSupport.Dickson.I271.TabMSeven in
theorem certificate17491 :
    fixAll (heChunk [0, 3, 5, 14]) (wV ()) = true :=
  (KernelKDenseP.HeSeven.fixAll_heChunk (by decide)).2.2

end Certificates
