module

public import CFSG.HardMathSupport.Dickson.Bal207.D42TriInputs
public import CFSG.Sporadic.SmallOddCore.CentSpec
import Certificates.Kernel.D42Tri.T2Glue
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModelBase

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Dickson.Bal207.D42Tri CFSG.EvenSmallLie.OmegaEight in
theorem certificate17629 : Nat.card (CFSG.Sporadic.Schreier.centralizerIn omegaT
    (CFSG.Sporadic.SmallOddCore.tp 360 (t2Tbl ()))) ≤ 431 :=
  KernelD42Tri.card_centralizer_t2_le'

end Certificates
