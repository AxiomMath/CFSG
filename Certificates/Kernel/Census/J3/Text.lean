module

public import CFSG.Sporadic.Schreier.PairJ3CertInputs
public import CFSG.Sporadic.SmallOddCore.J3DataInputs
public meta import CFSG.Sporadic.Schreier.PairJ3CertInputs
public meta import CFSG.Sporadic.SmallOddCore.J3DataInputs
public meta import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelCensus.J3S CFSG.Sporadic.Schreier.j3StrongHex

#kmisc_hexflat CertificateChecks.KernelCensus.J3S CFSG.Sporadic.Schreier.j3StrongHex 4 6156 13 5

#ks_chars CertificateChecks.KernelCensus.J3UT CFSG.Sporadic.SmallOddCore.j3CentHex

#kmisc_hexflat CertificateChecks.KernelCensus.J3UT CFSG.Sporadic.SmallOddCore.j3CentHex 4 6156 13 1

end
