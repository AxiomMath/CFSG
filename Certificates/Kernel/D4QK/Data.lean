module

public import Certificates.Data.Kernel.SporSch.Co1MatW
public meta import Certificates.Kernel.SporSch.Co1.GenBfs
public meta import CFSG.Quasithin.Background.Harris.R1.D4ModelCheck
meta import Certificates.Kernel.D4QK.In
public import CFSG.Open.LocalVocabulary
public import Certificates.Kernel.SporSch.Co1.GenBfs

public section

set_option maxRecDepth 400000

#kss_co1gt CertificateChecks.KernelD4Q.QT CFSG.Quasithin.Background.Harris.R1.D4Vert.qGensA 2049
#kss_co1gt CertificateChecks.KernelD4Q.KT CFSG.Quasithin.Background.Harris.R1.D4Vert.kGens 43
#kss_co1gt CertificateChecks.KernelD4Q.BT CFSG.Quasithin.Background.Harris.R1.D4Vert.bGens 28673
#kss_co1gt CertificateChecks.KernelD4Q.ST CFSG.Quasithin.Background.Harris.R1.D4Vert.sGensA 2049
#kss_co1gt CertificateChecks.KernelD4Q.ZT CertificateChecks.KernelD4Q.zArr 8

end
