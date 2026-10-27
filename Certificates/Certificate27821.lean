module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWClsCheck
import Certificates.Kernel.Census.Pg.ClsFacts
import Certificates.Kernel.Census.Pg.ClsOrb
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.CFSGNative.Perm.Chain
public import Mathlib
import CFSG.Certificates.Kernel.Spor.RawOrbGrp
import Certificates.Kernel.Census.Pg.Facts

public section

namespace Certificates

open CertificateChecks

theorem certificate27821 : CFSG.EvenSporadicStandard.Fin76b.W16.repCheck = true ∧
    CFSG.EvenSporadicStandard.Fin76b.W16.fpDistinct = true ∧
    CFSG.EvenSporadicStandard.Fin76b.W16.sumCheck = true ∧
    CFSG.EvenSporadicStandard.Fin76b.W16.centCheck = true ∧
    CFSG.EvenSporadicStandard.Fin76b.W16.involCheck = true :=
  KernelPgCls.cert27821

end Certificates
