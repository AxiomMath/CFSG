module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterElevenInputs
import Certificates.Certificate6007
import Certificates.Kernel.KDenseP.E11
public import CFSG.YGroups.DCE.MaximalB
public import CFSG.YGroups.Y443.Native.AlignB
public import CFSG.YGroups.Y443.Native.AlignW
public import CFSG.YGroups.Y443.Native.CosetData
public import CFSG.YGroups.Y443.Native.Image

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterEleven in
theorem certificate16955 : elevenDataCheck () = true :=
  KernelKDenseP.E11.c16955

end Certificates
