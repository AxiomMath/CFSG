module

public import CFSG.Sporadic.ThSchreier.GlobalData
import Certificates.Certificate1021
import CFSG.Assembly.Defs
import CFSG.Sporadic.Th.KernelPlanes

public section

namespace Certificates

theorem certificate2323 : CFSG.Sporadic.ThSchreier.planeX.ncard = 143127000 :=
  CFSG.Sporadic.Th.Kernel.ncard_planeX th_kernel_facts_ok

end Certificates
