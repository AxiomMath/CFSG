
module

public import Certificates.Certificate7019Base
import Certificates.Kernel.J4Count.FuseBase
import CFSG.Sporadic.Schreier.J4SOrbitsBase
meta import CFSG.Sporadic.Schreier.J4SOrbitsBase

public import CFSG.Quasithin.H13.J4FixSpec
public import CFSG.Sporadic.Schreier.J4SLocal
import Certificates.Kernel.J4Count.Fuse
import CFSG.Sporadic.Schreier.J4SNative
import CFSG.Sporadic.Schreier.J4SCols
import CFSG.Sporadic.Schreier.J4SFormData
import CFSG.Sporadic.Schreier.J4SNoCompData
meta import CFSG.Sporadic.Schreier.J4SNoCompData
import CFSG.Sporadic.Schreier.J4SOrbits
meta import CFSG.Sporadic.Schreier.J4SOrbits
import CFSG.Sporadic.J4.QT2LocX0KNative
import CFSG.Sporadic.J4.QTNative
import CFSG.Sporadic.J4.QT2LocX0CheckInputs
public import CFSG.Sporadic.Schreier.J4SOrderBase
import CFSG.Quasithin.H13.J4Classes
import Certificates.Kernel.J4Count.FixZKBase
import Certificates.Kernel.J4Count.FuseBase1

public section

namespace Certificates

open CertificateChecks

theorem certificate7019 :
    Nat.card {w : CFSG.Sporadic.J4.Row //
      w ∈ MulAction.orbit CFSG.Sporadic.J4.J CFSG.Sporadic.J4Schreier.v ∧
        CFSG.Quasithin.H13.J4.tJ • w = w} = 52349 := KernelJ4Count.Fuse.card_fix_tJ'

end Certificates
