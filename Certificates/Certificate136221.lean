module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThreeBWords
import Certificates.Certificate6007
import Certificates.Kernel.KDenseP.MonThreeB
public import CFSG.YGroups.Y443.Native.EdgeNoncomm

public section

namespace Certificates

open CertificateChecks

open CFSG.Monster.AxisCount CFSG.AGLEmbedding.Norton.MON5_7 CFSG.YGroups.Y443
  CFSG.YGroups.Y443Native CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF in
theorem certificate136221 :
    agreeAll ((m3bEqs.drop 8).take 18) = true := KernelKDenseP.MonThreeB.c136221

end Certificates
