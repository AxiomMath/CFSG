module

public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersThData
import Certificates.Kernel.LocalComp.ThOrderSound
public import Certificates.Data.CFSGNative.SectionRank.Th

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.CatalogOrders CFSG.SectionRank.Native in
theorem certificate3005 : prodOrderOK (ops2 248) thData.seedA thData.seedB 19 0 = true := KernelLC.cert3005

end Certificates
