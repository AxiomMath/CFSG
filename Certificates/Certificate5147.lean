module

public import CFSG.GH74.GLS.LU.Local.FiveStdInputs
public meta import CFSG.GH74.GLS.LU.Local.FiveStdInputs
import Certificates.Kernel.FiveStd.RepGlue
public import Mathlib.Data.Fin.Basic
public meta import Mathlib.Data.Fin.Basic
public import Mathlib.Data.List.Basic
public meta import Mathlib.Data.List.Basic

public section

namespace Certificates

open CertificateChecks

theorem certificate5147 : CFSG.GH74.GLS.LU.Local.FiveStd.fiveStdCheck = true := FiveStd.five_std_check

end Certificates
