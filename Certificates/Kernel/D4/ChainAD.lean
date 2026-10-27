module

public import Certificates.Data.Item434D42
public import Certificates.Kernel.Sporadic.RawGenSplit
public meta import Certificates.Data.Item434D42

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelD4

@[expose] def dA : List (List Int) :=
  CFSG.RankThree.PartTwo.Sec4.Item434D42.d4ChainAWords.toList.drop 2

end CertificateChecks.KernelD4

end

#ks_rawchain_sl2_data CertificateChecks.KernelD4.CA 2457 12 16 256
  CFSG.RankThree.PartTwo.Sec4.Item434D42.d4ChainAArrs
  CFSG.RankThree.PartTwo.Sec4.Item434D42.d4ChainABaseArr 2 CertificateChecks.KernelD4.dA
