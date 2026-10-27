module

public import CFSG.Monster.GMS.R433Cover.Y432IdentitiesInputs
public import CFSG.Monster.GMS.R433Cover.Y432Transport
public import CFSG.YGroups.Exact.Y432Inputs
import Certificates.Kernel.YModel.C10036

public section

namespace Certificates

open CertificateChecks

open CFSG.YGroups CFSG.Monster.GMS.R433Cover CFSG.Monster.B.Co2.Native in
theorem certificate10036 :
    (eqA 31673
      (ModelNative.evalW 31673 y432Arrays
      (List.replicate 3 ((List.replicate 5 (spiderWord 4 3)).flatten ++ [0])).flatten)
      (idA 31673) = true)
    ∧ (eqA 31673 (ModelNative.evalW 31673 y432Arrays (yConj.reverse ++ [0, 4, 6] ++ yConj))
      (ModelNative.evalW 31673 y432Arrays ([2, 5, 7, 9] ++ f213Word)) = true) := KernelYModel.c10036

end Certificates
