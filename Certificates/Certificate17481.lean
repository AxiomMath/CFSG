module

public import CFSG.YGroups.Y443.Native.Words
public import Certificates.Data.TabMSevenHe
import Certificates.Kernel.KDenseP.HeSeven

public section

namespace Certificates

open CertificateChecks

open CFSG.YGroups.Y443 CFSG.YGroups.Y443Native CFSG.HardMathSupport.Dickson.I271.TabMSeven in
theorem certificate17481 :
    fixAll (heChunk [1, 2, 5, 6]) (aV ()) = true :=
  (KernelKDenseP.HeSeven.fixAll_heChunk (by decide)).1

end Certificates
