module

public import Certificates.Data.Kernel.Fi24PDc2.Defs
public import Certificates.Data.Kernel.SporLatDc2Check
public import CFSG.Sporadic.FischerOddCore.Fi24R2Data
import Certificates.Kernel.Fi24PDc2.Final
import Certificates.Kernel.Sporadic.Fi24K.C2077
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace Certificates

open CFSG.KD.Fi24PDc2 in
theorem certificate10511 :
    CFSG.KC.SLD2.dc2Check C CFSG.KD.Fi24PDc2.D = true ∧
    (∀ l < 2, ∀ p < 378,
      (CFSG.Sporadic.FischerOddCore.fi24PStrong[l]!)[p]! = CFSG.KD.Fi24PDc2.L (Nat.add 6 l) p) ∧
    CFSG.KD.Fi24PDc2.shapeOK = true ∧ CFSG.KD.Fi24PDc2.letOK = true ∧ CFSG.KD.Fi24PDc2.D.sep = [0, 1, 2, 5] ∧ sbOK = true ∧
    SB.C.flatten.length = 256 := CFSG.KD.Fi24PDc2.facts

end Certificates
