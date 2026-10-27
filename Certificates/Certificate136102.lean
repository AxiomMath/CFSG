module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveRel
import Certificates.Certificate6007
import Certificates.Kernel.KDenseP.MonFive
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.AgreeTasks
public import CFSG.YGroups.DCE.MaximalB
public import CFSG.YGroups.Y443.Native.AlignB
public import CFSG.YGroups.Y443.Native.AlignW
public import CFSG.YGroups.Y443.Native.CosetData
public import CFSG.YGroups.Y443.Native.Image

public section

namespace Certificates

open CertificateChecks

open CFSG.AGLEmbedding.Norton.MON5_7 CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFive in
theorem certificate136102 :
    agreeAll (relSeg 35 6) = true := KernelKDenseP.MonFive.c136102

end Certificates
