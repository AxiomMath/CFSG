module

public import CFSG.Sporadic.Recognition.Fi22MultiplierInputs
public import CFSG.YGroups.Exact.Y332Inputs
import Certificates.Kernel.YModel.Y332

public section

namespace Certificates

open CertificateChecks

open CFSG.YGroups CFSG.Sporadic.Recognition.Fi22Multiplier CFSG.Monster.B.Co2.Native in
theorem certificate24050 :
    (eqA 28162
      (ModelNative.evalW 28162 y332Arrays
        (List.replicate 3 ((List.replicate 5 (spiderWord 3 3)).flatten ++ [0])).flatten)
      (idA 28162) = true)
    ∧ (eqA 28162 (ModelNative.evalW 28162 y332Arrays (y332Conj.reverse ++ [0, 3, 8] ++ y332Conj))
      (ModelNative.evalW 28162 y332Arrays ([3, 4, 6, 8] ++ f332Word)) = true)
    ∧ (eqA 28162 (ModelNative.evalW 28162 y332Arrays f332Word) (idA 28162) = false) := KernelYModel.c24050

end Certificates
