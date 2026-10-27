module

public import CFSG.Sporadic.Co2Schreier.ClassCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.ThirdCheck
public meta import CFSG.Sporadic.Co2InvData
import Certificates.Kernel.SporSch.Co2M.Class
public import CFSG.Assembly.Defs

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Co2Schreier CFSG.Monster.B.Co2.Native CFSG.Certificates.Native in
open CFSG.Monster.B.Mathieu CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2.Native in
theorem certificate2050 : classCheck co2PosTable zArr tArr uArr = true := KernelSporSch.Co2M.class_check

end Certificates
