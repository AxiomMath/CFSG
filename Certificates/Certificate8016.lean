module

public import Certificates.Data.CFSGNative.SectionRank.Fi24prime
import Certificates.Kernel.LocalComp.Fi24.Elem
public import CFSG.Open.LocalVocabulary

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.SectionRank CFSG.Open CFSG.SectionRank.Native in
theorem certificate8016 : (ops3 781).check fi24primeData = true := KernelLC.F24.check

end Certificates
