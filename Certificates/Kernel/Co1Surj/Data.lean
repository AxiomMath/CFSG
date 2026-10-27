module

public import Certificates.Kernel.LocalComp.SurjGen
public import Certificates.Data.CFSGNative.Bridge.SurjD
meta import Certificates.Data.CFSGNative.Bridge.SurjD

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelCo1Surj.IT CFSG.Sporadic.Bridge.SurjD.Native.co1ImgText
#ks_chars CertificateChecks.KernelCo1Surj.ST CFSG.Sporadic.Bridge.SurjD.Native.co1SurjText
#lc_words CertificateChecks.KernelCo1Surj.IW CFSG.Sporadic.Bridge.SurjD.Native.co1ImgText
#lc_words CertificateChecks.KernelCo1Surj.SW CFSG.Sporadic.Bridge.SurjD.Native.co1SurjText

end
