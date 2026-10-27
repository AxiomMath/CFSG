module

public import CFSG.LocalAnalysis.StandardType.GGStepTwoToralCertSound

public section

namespace CFSG.StandardType.StepTwoToralCert

open CFSG.Blueprint.Chevalley

theorem certAll_of_specs
    (h1 : SplitCertSpec .F4 3 ⊤ ∧ SplitCertSpec .E6 3 ⊤ ∧ SplitCertSpec .E6 5 ⊤ ∧
      SplitCertSpec .E7 3 ⊤ ∧ SplitCertSpec .E7 5 ⊤ ∧ SplitCertSpec .E7 7 ⊤ ∧
      SplitCertSpec .E8 3 ⊤ ∧ SplitCertSpec .E8 5 ⊤)
    (h2 : TwistCertSpec 3 e6Gamma ∧ TwistCertSpec 5 e6Gamma) (h3 : splitT0OK = true)
    (h4 : SplitCertSpec .E8 7 ⊤) : CertAll :=
  ⟨h1.1, ⟨h1.2.1, splitCertSpecT0_of_check h3, h1.2.2.1⟩,
    ⟨h1.2.2.2.1, h1.2.2.2.2.1, h1.2.2.2.2.2.1⟩, ⟨h1.2.2.2.2.2.2.1, h1.2.2.2.2.2.2.2, h4⟩,
    h2.1, h2.2⟩

end CFSG.StandardType.StepTwoToralCert
