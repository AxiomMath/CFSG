module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenInputs
import Certificates.Certificate6007
import Certificates.Kernel.KDenseP.MonThreeB
public import CFSG.YGroups.Y443.Native.EdgeNoncomm

public section

namespace Certificates

open CertificateChecks

open CFSG.AGLEmbedding.Norton.MON5_7 CFSG.YGroups.Y443 CFSG.YGroups.Y443Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance in
theorem certificate13638 : agreeAll m7APairs = true ∧ EdgeNoncomm.moveCheck m7rbW (aV ()) = true ∧
    EdgeNoncomm.moveCheck m7rtbW (aV ()) = true := KernelKDenseP.MonThreeB.c13638

end Certificates
