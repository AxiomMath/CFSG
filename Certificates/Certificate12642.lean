module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.KS1523.SCentInputs
import Certificates.Kernel.Misc.Perm.SCent12642

public section

namespace Certificates

open CertificateChecks

theorem certificate12642 : CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KS1523.sCentOK = true :=
  KernelMisc.SCent12642.sCent_true

end Certificates
