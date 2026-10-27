module

public import Certificates.Data.TriD4TwoRow
public import Certificates.Kernel.B3S3.GenSl
public meta import Certificates.Data.TriD4TwoRow

public section

namespace CertificateChecks.KernelD4

meta def s0GensM : Array (Array ℕ) := CFSG.StandardType.TriD4TwoRow.s0Gens ()

end CertificateChecks.KernelD4

end

set_option maxRecDepth 400000

#kb3_enum_sl CertificateChecks.KernelD4.ES CertificateChecks.KernelD4.s0GensM
  CFSG.RankThree.PartTwo.Sec4.Item434D42.d4ChainABaseArr 2457 12 27
