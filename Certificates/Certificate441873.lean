module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CompatModel.Gen2ACheck
import Certificates.Kernel.HN1408.Gen2A

public section

namespace Certificates

open CFSG.EvenSporadicStandard.HNRecog.CompatModel in
theorem certificate441873 : gen2aOK = true :=
  CFSG.KD.HN1408.gen2aOK_of

end Certificates
