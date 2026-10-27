module

public import Certificates.Data.McLCover3
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public meta import Certificates.Data.McLCover3
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelCover3.MC CFSG.SectionRank.QTK.Insp443.McLCover.mclCovHex
#kmisc_hexflat CertificateChecks.KernelCover3.MC
  CFSG.SectionRank.QTK.Insp443.McLCover.mclCovHex 3 275 9 5
