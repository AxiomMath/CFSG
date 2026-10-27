module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.MonsterFiveBWitData
import Certificates.Certificate6007
import Certificates.Kernel.KDenseP.MonFiveB
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.AgreeTasks
public import CFSG.YGroups.DCE.MaximalB
public import CFSG.YGroups.Y443.Native.AlignB
public import CFSG.YGroups.Y443.Native.AlignW
public import CFSG.YGroups.Y443.Native.CosetData
public import CFSG.YGroups.Y443.Native.Image

public section

namespace Certificates

open CertificateChecks

open CFSG.AGLEmbedding.Norton.MON5_7 CFSG.HardMathSupport.Dickson.I271.MonsterFiveB in
theorem certificate17543 :
    ∀ e ∈ bEqsOf [6, 20], CFSG.Monster.AxisCount.wordLin e.1 = CFSG.Monster.AxisCount.wordLin e.2 := KernelKDenseP.MonFiveB.c17543

end Certificates
