module

public import CFSG.HardMathSupport.Dickson.BMRows.M11M12Inputs
import Certificates.Certificate6007
import Certificates.Kernel.KDenseP.CM12
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterElevenInputs
public import CFSG.YGroups.DCE.MaximalB
public import CFSG.YGroups.Y443.Native.AlignB
public import CFSG.YGroups.Y443.Native.AlignW
public import CFSG.YGroups.Y443.Native.CosetData
public import CFSG.YGroups.Y443.Native.Image

public section

namespace Certificates

open CertificateChecks

theorem certificate17702 :
    CFSG.HardMathSupport.Dickson.BMRows.M11.m12Check () = true :=
  KernelKDenseP.CM12.c17702

end Certificates
