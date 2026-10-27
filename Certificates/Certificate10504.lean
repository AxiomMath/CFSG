module

public import Certificates.Data.Kernel.McLDc2.Defs
public import Certificates.Data.Kernel.SporLatDc2Check
public import CFSG.Sporadic.Schreier.PairMcLCertInputs
import Certificates.Kernel.McLDc2.Final
import Certificates.Kernel.Misc.Perm.HSMcL
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace Certificates

open CFSG.KD.McLDc2 in
theorem certificate10504 :
    CFSG.KC.SLD2.dc2Check C CFSG.KD.McLDc2.D = true ∧
    (∀ l < 2, ∀ p < 275, (CFSG.Sporadic.Schreier.mclStrongArrs[l]!)[p]! = CFSG.KD.McLDc2.L (Nat.add 5 l) p) ∧
    CFSG.KD.McLDc2.shapeOK = true ∧ letOK = true ∧ CFSG.KD.McLDc2.D.sep = [0, 1, 2, 3, 4] ∧ sbOK = true ∧
    SB.C.flatten.length = 128 := CFSG.KD.McLDc2.facts

end Certificates
