module

public import CFSG.Sporadic.Th.Setup
import Certificates.Certificate1021
import CFSG.Assembly.Defs

public section

namespace Certificates

theorem certificate9013 : Nat.card CFSG.Sporadic.Th.J = 90745943887872000 :=
  CFSG.Sporadic.Th.Kernel.card_J_eq th_kernel_facts_ok

end Certificates
