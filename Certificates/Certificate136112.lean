module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveRepDef
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

open CFSG.AGLEmbedding.Norton.MON5_7 CFSG.YGroups.Y443 CFSG.YGroups.Y443Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFive in
theorem certificate136112 :
    EdgeNoncomm.moveCheck fiveGens[8]! (aV ()) = true := KernelKDenseP.MonFive.c136112

end Certificates
