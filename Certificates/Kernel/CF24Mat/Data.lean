module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.LocalComp.SurjGen
public import Certificates.Data.GSThmBCatalog7CF24
meta import Certificates.Data.CFSGNative.Bridge.SuzGPL

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelCF24M.AT CFSG.ComponentClassification.GSThmB.CF24.cf24AText
#ks_chars CertificateChecks.KernelCF24M.BT CFSG.ComponentClassification.GSThmB.CF24.cf24BText
#ks_chars CertificateChecks.KernelCF24M.IT CFSG.Sporadic.Bridge.SuzGPL.Native.imgText
#lc_words CertificateChecks.KernelCF24M.IT CFSG.Sporadic.Bridge.SuzGPL.Native.imgText

end
