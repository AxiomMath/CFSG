module

public import CFSG.GH74.E2.Cl2Quot
public import CFSG.GH74.E2.FrattiniRank
public import CFSG.GH74.E2.DirectProd
public import CFSG.CharacterTheory.Semidihedral.Presentation
public import CFSG.CharacterTheory.Semidihedral.NormalForm
public meta import Mathlib
public import CFSG.GH74.E2.Alpha1AutCertInputs
import CFSG.Certificates.Kernel.SD16Code
import CFSG.Certificates.Kernel.Common.Loop
meta import CFSG.Certificates.Kernel.Common.Harness
import CFSG.CharacterTheory.Semidihedral.Model
public import CFSG.GH74.E2.SD16Cert

open CFSG.GH74.E2 CFSG.Semidihedral CFSG.KS.SD16Code

namespace CertificateChecks.Batch5004

open CFSG.GH74.E2 CFSG.Semidihedral CFSG.KS.SD16Code

local instance instDecEqSD16MFor5004 : DecidableEq SD16M := inferInstance

end CertificateChecks.Batch5004

