module

public import CFSG.YGroups.Y443.Native.Words
public import Certificates.Data.TabMSevenHe
import Certificates.Kernel.KDenseP.HeSeven

public section

namespace Certificates

open CertificateChecks

open CFSG.YGroups.Y443 CFSG.YGroups.Y443Native CFSG.HardMathSupport.Dickson.I271.TabMSeven in
theorem certificate17490 :
    fixAll (heChunk [6, 7, 9, 12]) (CFSG.YGroups.Y443Native.bV ()) = true :=
  (KernelKDenseP.HeSeven.fixAll_heChunk (by decide)).2.1

end Certificates
