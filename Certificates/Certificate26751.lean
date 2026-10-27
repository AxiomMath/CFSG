module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S9Check
import Certificates.Kernel.TwoHS.E1Glue

public section

namespace Certificates

open CFSG.EvenSporadicStandard.TwoHS in
theorem certificate26751 : e1OK = true ∧ realOK = true :=
  ⟨CFSG.KD.TwoHS.e1OK_true, CFSG.KD.TwoHS.realOK_true⟩

end Certificates
