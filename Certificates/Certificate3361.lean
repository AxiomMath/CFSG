module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneOqDataSylow
import Certificates.Kernel.Misc.Sp6Bridge
import Certificates.Data.Kernel.Misc.Sp6
import Certificates.Kernel.Misc.Sp6Data
import CFSG.Certificates.Kernel.Common.Harness
public import Mathlib.Data.Nat.Bitwise

public section

namespace Certificates

open CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne in
theorem certificate3361 : (pCheck false = true)
    ∧ (pCheck true = true)
    ∧ (eaCheck false = true)
    ∧ (eaCheck true = true)
    ∧ (boundCheck false = true)
    ∧ (boundCheck true = true) := CFSG.KD.Misc.Sp6.facts

end Certificates
