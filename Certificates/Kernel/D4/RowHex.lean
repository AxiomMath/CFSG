module

public import Certificates.Data.TriD4TwoRow
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Data.TriD4TwoRow

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelD4.RX CFSG.StandardType.TriD4TwoRow.rowHex
#kmisc_hexflat CertificateChecks.KernelD4.RX CFSG.StandardType.TriD4TwoRow.rowHex 3 2457 12 53
