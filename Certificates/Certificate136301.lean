module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenChecks
import Certificates.Certificate6007
import Certificates.Kernel.KDenseP.MonSeven
public import CFSG.YGroups.Y443.Native.EdgeNoncomm

public section

namespace Certificates

open CertificateChecks

open CFSG.AGLEmbedding.Norton.MON5_7 CFSG.YGroups.Y443 CFSG.YGroups.Y443Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenChecks in
theorem certificate136301 :
    agreeAll (orbPairs 11 22) = true := KernelKDenseP.MonSeven.c136301

end Certificates
