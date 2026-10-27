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
theorem certificate13695 :
    agreeAll pcPairs = true ∧ agreeAll autPairs = true ∧ agreeAll ratPairs = true := KernelKDenseP.MonSeven.c13695

end Certificates
