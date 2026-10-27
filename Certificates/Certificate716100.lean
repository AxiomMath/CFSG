module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenFlag
import Certificates.Kernel.KDenseP.MonSevenB
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.WordCheck

public section

namespace Certificates

open CertificateChecks

open CFSG.AGLEmbedding.Norton.MON5_7
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenFlag in
theorem certificate716100 : agreeAll m7hPairs = true := KernelKDenseP.MonSeven.c716100

end Certificates
