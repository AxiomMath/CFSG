module

public import CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition.ModelTuple
import Certificates.Kernel.J3ModelGen.Fact
public import Certificates.Certificate3169

public section

namespace Certificates

open CertificateChecks

open CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition in
theorem certificate272032 : SatisfiesJ3Words uJ ∧ Subgroup.closure (Set.range uJ) = ⊤ := KernelJ3ModelGen.facts

end Certificates
