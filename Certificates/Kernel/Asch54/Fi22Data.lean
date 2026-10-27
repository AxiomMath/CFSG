module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.Asch54SporFi22
public meta import Certificates.Data.Asch54SporFi22
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.A54F22X CFSG.LocalAnalysis.WeakClosure81.Asch54Fi22.a0GenHex

#kmisc_hexflat CertificateChecks.KernelSpor.A54F22X
  CFSG.LocalAnalysis.WeakClosure81.Asch54Fi22.a0GenHex 3 3510 12 2

#ks_chars CertificateChecks.KernelSpor.A54F22M CFSG.LocalAnalysis.WeakClosure81.Asch54Fi22.mHex

#kmisc_hexflat CertificateChecks.KernelSpor.A54F22M
  CFSG.LocalAnalysis.WeakClosure81.Asch54Fi22.mHex 3 3510 12 1

namespace CertificateChecks.KernelSpor.A54F22

open CFSG.LocalAnalysis.WeakClosure81.Asch54Fi22 CFSG.Certificates.Native

meta def regs : Array (Array Nat) := slpStrong 3510 genOrig genWords

meta def regsI : Array (Array Nat) := rawInvs 3510 regs

end CertificateChecks.KernelSpor.A54F22

#kmisc_packarrs CertificateChecks.KernelSpor.A54F22.R CertificateChecks.KernelSpor.A54F22.regs 12

#kmisc_packarrs CertificateChecks.KernelSpor.A54F22.RI CertificateChecks.KernelSpor.A54F22.regsI 12

end
