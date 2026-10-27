module

public import Certificates.Data.Co3Cent
public meta import Certificates.Data.Co3Cent
public meta import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelCo3Cent.CH CFSG.HardMathSupport.Dickson.I271.Co3Cent.hex

#kmisc_hexflat CertificateChecks.KernelCo3Cent.CH CFSG.HardMathSupport.Dickson.I271.Co3Cent.hex 3 276 9 38

end
