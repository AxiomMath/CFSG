module

public import Certificates.Data.J3Cover3
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.Sporadic.IntWordsCmd
public meta import Certificates.Data.J3Cover3
public meta import Certificates.Kernel.J3Ref.Bind
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.J3Ref.Bind

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelCover3.JC CFSG.SectionRank.QTK.Insp443.J3Cover.j3CovHex
#kmisc_hexflat CertificateChecks.KernelCover3.JC
  CFSG.SectionRank.QTK.Insp443.J3Cover.j3CovHex 4 6156 13 6

namespace CertificateChecks.KernelCover3

open CFSG.SectionRank.QTK.Insp443.J3Cover

meta def j3WordsM : Array (List Int) :=
  (Array.range 6).map fun k => CertificateChecks.KernelJ3Ref.siftWordM (j3CovArr k)

meta def j3ProdsM : Array (Array Nat) := (Array.range 9).map j3CovProd

end CertificateChecks.KernelCover3

#kc_intwords CertificateChecks.KernelCover3.JW CertificateChecks.KernelCover3.j3WordsM
#kmisc_packarrs CertificateChecks.KernelCover3.JD CertificateChecks.KernelCover3.j3ProdsM 13
