module

public import CFSG.RankThree.Native.ONThreeInputs
import Certificates.Kernel.ONSeven.C9702

public section

namespace Certificates

open CertificateChecks

open CFSG.RankThree.Native CFSG.ONSchreier CFSG.ONSchreier.Native in
theorem certificate9702 : onThreeCommOK (onSevenArr [6]) = true ∧
    onThreeTreeOK onThreeYArrs onThreeTreePts onThreeTreePar onThreeTreeGen = true ∧
    onThreeCovers (onSevenArr [6]) onThreeTreePts = true :=
  KernelSpor.ONS.facts9702

end Certificates
