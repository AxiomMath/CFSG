module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S6Data
import Certificates.Kernel.HS3850.S25950Facts

public section

namespace Certificates

open CFSG.EvenSporadicStandard.TwoHS in
theorem certificate25950 : (s6WSq = true) ∧ (s6Strong = true) ∧ (s6XRel = true) ∧ (s6Fix = true) :=
  ⟨CFSG.KD.HS3850.wsq_true, CFSG.KD.HS3850.strong_true, CFSG.KD.HS3850.xrel_true,
    CFSG.KD.HS3850.fix_true⟩

end Certificates
