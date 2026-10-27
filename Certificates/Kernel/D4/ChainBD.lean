module

public import Certificates.Data.Item434D42
public import Certificates.Kernel.Sporadic.RawGenSplit
public meta import Certificates.Data.Item434D42

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelD4

@[expose] def dB : List (List Int) :=
  CFSG.RankThree.PartTwo.Sec4.Item434D42.d4ChainBWords.toList.drop 2

end CertificateChecks.KernelD4

end

#ks_rawchain_sl2_data CertificateChecks.KernelD4.CB 2457 12 0 256
  CFSG.RankThree.PartTwo.Sec4.Item434D42.d4ChainBArrs
  CFSG.RankThree.PartTwo.Sec4.Item434D42.d4ChainBBaseArr 2 CertificateChecks.KernelD4.dB
