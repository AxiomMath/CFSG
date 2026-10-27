module

public import Certificates.Data.Sp62.Transvections
import CFSG.Certificates.Kernel.Sp62X2.Sound
import Certificates.Kernel.Sp6Two.Final
import Certificates.Kernel.Sp62X2.Checks

public section

open CFSG.Quasithin.H13.U3

namespace Certificates

open CFSG.Quasithin.H13.U3 in
theorem certificate4196 : sp62X2OK = true :=
  CFSG.KC.Sp62X2.x2Test CFSG.KD.Sp6Two.orb0_8151.2.1 CFSG.KD.Sp6Two.orb0_8151.2.2
    CFSG.KD.Sp6Two.orb2_8151.2.1 CFSG.KD.Sp6Two.orb2_8151.2.2 CFSG.KD.Sp62X2.ch4196_x2
    (by decide)

end Certificates
