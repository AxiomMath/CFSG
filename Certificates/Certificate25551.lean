module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.OddFixData
import Certificates.Kernel.HS3850.Q25551Facts

public section

namespace Certificates

open CFSG.EvenSporadicStandard.TwoHS in
theorem certificate25551 : (hsOdd1PowA = true) ∧ (hsOdd1PowB = true) ∧ (hsOdd1PowAB = true) ∧
    (hsOdd1Quart = true) :=
  ⟨CFSG.KD.HS3850.powA_true, CFSG.KD.HS3850.powB_true, CFSG.KD.HS3850.powAB_true,
    CFSG.KD.HS3850.quart_true⟩

end Certificates
