module

public import Certificates.Data.Kernel.Fi22Dc2.Defs
public import Certificates.Data.Kernel.SporLatDc2Check
public import CFSG.Monster.B.Fischer.Fi22OuterArrays
public import CFSG.Monster.B.Fischer.PinnedChainInputs
import Certificates.Kernel.Fi22Dc2.Final
import Certificates.Kernel.Sporadic.Fi22.X2069Ext
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Sporadic.Fi22.C2068
import Certificates.Kernel.Sporadic.Fi22.C3151

public section

namespace Certificates

open CFSG.KD.Fi22Dc2 in
theorem certificate10505 :
    CFSG.KC.SLD2.dc2Check C CFSG.KD.Fi22Dc2.D = true ∧ CFSG.KD.Fi22Dc2.permOK = true ∧
    (∀ j < 9, ∀ p < 3510, CFSG.KD.Fi22Dc2.P (((CFSG.Monster.B.Fischer.fi22OuterStrong3510 4)[j]!)[Q p]!) =
      CFSG.KC.E64F.wordF CFSG.KD.Fi22Dc2.L (CFSG.KD.Fi22Dc2.tw j) p) ∧
    (∀ k < 2, ∀ p < 3510, CFSG.KD.Fi22Dc2.L (5 + k) p = CFSG.KD.Fi22Dc2.P ((CFSG.Monster.B.Fischer.fi22StrongArrs[k]!)[Q p]!)) ∧
    hwOK = true ∧ CFSG.KD.Fi22Dc2.D.sep = [0, 1, 2, 3, 6, 4].map CFSG.KD.Fi22Dc2.P := CFSG.KD.Fi22Dc2.facts

end Certificates
