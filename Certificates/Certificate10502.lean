module

public import Certificates.Data.Kernel.SuzDc2.Defs
public import Certificates.Data.Kernel.SporLatDc2Check
public import CFSG.Sporadic.SuzOddCore.Arrays
import Certificates.Kernel.SuzDc2.Final
import Certificates.Kernel.SuzDc2.Slices
import Certificates.Kernel.Sporadic.OddCore.SuzCert
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace Certificates

open CFSG.KD.SuzDc2 in
theorem certificate10502 :
    CFSG.KC.SLD2.dc2Check C D = true ∧
    (∀ l < 2, ∀ p < 22880, (CFSG.Sporadic.SuzOddCore.certArr l)[p]! = CFSG.KD.SuzDc2.L (Nat.add 6 l) p) ∧
    CFSG.KD.SuzDc2.shapeOK = true ∧ letOK = true ∧ D.sep = [0, 1, 2, 3, 4, 5] ∧ sbOK = true ∧
    SB.C.flatten.length = 8192 := CFSG.KD.SuzDc2.facts

end Certificates
