module

public import CFSG.Sporadic.Recognition.J4MultiplierInputs
public import Certificates.Data.Kernel.CosetJ.F2Cert
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import CFSG.Open.Defs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCosetJ.J4

open CFSG.Sporadic.J4Schreier CFSG.Sporadic.Recognition.J4Multiplier CFSG.KC.CosetJ.F2

@[expose] def ws : List (List Bool) :=
  [[false, false], [true, true, true], [false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true], [false, true, true, false, true, true,
  false, true, false, true, false, true, true, false, true, true, false, true, false, true, false,
  true, true, false, true, true, false, true, false, true, false, true, true, false, true, true,
  false, true, false, true, false, true, true, false, true, true, false, true, false, true],
  [false, true, false, true, false, true, true, false, true, false, true, false, true, true,
  false, true, false, true, false, true, true, false, true, false, true, true, false, true, true,
  false, true, false, true, true, false, true, true, false, true, false, true, true, false, true,
  true], [false, true, false, true, false, true, true, false, true, false, true, true, false,
  true, false, true, true, false, true, false, true, false, true, true, false, true, false, true,
  true, false, true, false, true, true, false, true, false, true, false, true, true, false, true,
  false, true, true, false, true, false, true, true, false, true, false, true, false, true, true,
  false, true, false, true, true, false, true, false, true, true]]

theorem fox_check :
    foxOK j4FoxX.toList j4FoxY.toList xColumns.toList yColumns.toList ws = true := by quickRfl

theorem form_check : formOK j4cSsym.toList j4cSdiag.toList j4cSA.toList j4cSB.toList
    xColumns.toList yColumns.toList = true := by quickRfl

end CertificateChecks.KernelCosetJ.J4

end
