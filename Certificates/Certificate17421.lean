module

public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.M13Inputs
import Certificates.Certificate6007
import Certificates.Kernel.KDenseP.MW
public import CFSG.YGroups.DCE.MaximalB
public import CFSG.YGroups.Y443.Native.AlignB
public import CFSG.YGroups.Y443.Native.AlignW
public import CFSG.YGroups.Y443.Native.CosetData
public import CFSG.YGroups.Y443.Native.Image

public section

namespace Certificates

open CertificateChecks

theorem certificate17421 :
    CFSG.HardMathSupport.Dickson.I271.m13Check () = true :=
  KernelKDenseP.MW.c17421

end Certificates
