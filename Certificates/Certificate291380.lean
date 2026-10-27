module

public import CFSG.Sporadic.Recognition.Fi22MultiplierInputs
public import CFSG.YGroups.Exact.Y332Inputs
import Certificates.Kernel.YModel.Y332

public section

namespace Certificates

open CertificateChecks

open CFSG.YGroups CFSG.Sporadic.Recognition.Fi22Multiplier CFSG.Monster.B.Co2.Native in
theorem certificate291380 :
    (∀ c < 9,
      eqA 28162 (ModelNative.evalW 28162 y332Arrays (f332Word ++ [c]))
        (ModelNative.evalW 28162 y332Arrays ([c] ++ f332Word)) = true)
    ∧ (eqA 28162 (ModelNative.evalW 28162 y332Arrays (f332Word ++ f332Word)) (idA 28162) = true) := KernelYModel.c291380

end Certificates
