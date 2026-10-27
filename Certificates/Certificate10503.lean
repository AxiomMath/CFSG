module

public import Certificates.Data.Kernel.Co2Dc2.Defs
public import Certificates.Data.Kernel.SporLatDc2Check
public import CFSG.Sporadic.Co2InvCheckInputs
import Certificates.Kernel.Co2Dc2.Final
import Certificates.Kernel.Sporadic.Co2Inv.Gens
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace Certificates

open CFSG.KD.Co2Dc2 in
theorem certificate10503 :
    CFSG.KC.SLD2.dc2Check C D = true ∧ permOK = true ∧
    (∀ j < 5, ∀ p < 2300,
      L j p = P ((CFSG.Sporadic.Co2Inv.genPermWith CFSG.Sporadic.Co2Cert.co2PosTable j)[Q p]!)) ∧
    (∀ k < 2, ∀ p < 2300, L (6 + k) p = P ((CFSG.Sporadic.Co2Cert.co2OrigArrs[k]!)[Q p]!)) ∧
    hwOK = true ∧ D.sep = [0, 1, 2, 3, 5, 4].map P := CFSG.KD.Co2Dc2.facts

end Certificates
