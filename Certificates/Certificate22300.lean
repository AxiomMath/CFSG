module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4FixL34Inputs
public meta import Certificates.Data.CFSGNative.PSL3Four.Certificate
import Certificates.Kernel.LocalComp.L34ScanFinal
import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions

public section

namespace Certificates

open CertificateChecks

open CFSG.PSL3Four.Native CFSG.ComponentClassification.CatFactsL4U4 in
theorem certificate22300 :
    fixCheck (enumBFS 42 gTabs 241920).tabs (centTabs 42 (enumBFS 42 gensS 20160).tabs r₂T)
        r₂T = true ∧
      fixCheck (enumBFS 42 gTabs 241920).tabs (centTabs 42 (enumBFS 42 gensS 20160).tabs r₃T)
        r₃T = true := KernelLC.L34Scan.fix_true

end Certificates
