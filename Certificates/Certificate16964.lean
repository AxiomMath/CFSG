
module

public import CFSG.GF2Type.Smith1979.GammaU.StepAFacts
import Certificates.Kernel.GammaUStepA.Glue

public section

namespace Certificates

open CFSG.GF2Type.Smith1979.GammaU.StepA in
theorem certificate16964 : StepATFacts :=
  ⟨CFSG.KD.GUA.t1_16964, CFSG.KD.GUA.t2_16964, CFSG.KD.GUA.t3_16964⟩

end Certificates
