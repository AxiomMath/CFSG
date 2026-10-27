module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2SevenData
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2SevenData
public meta import Certificates.Kernel.Co2Eleven.DataGen
meta import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Kernel.SporSch.Mathieu.Gen
public import Certificates.Kernel.Co2Eleven.DataGen
public import Mathlib
import Certificates.Kernel.Misc.Perm.HexCmd
import Certificates.Kernel.SporSch.Mathieu.Gen

public section

namespace CertificateChecks.KernelCo2Eleven

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2SevenNative

meta def d7 := co2SevenData
meta def wv7 : Array (Array Nat) := wvOf d7.words
meta def wvi7 : Array (Array Nat) := wviOf d7.words
meta def rec7 : Array (Array Nat) := recOf d7.words d7.is d7.ih d7.chain 7
meta def sz7 : Array Nat := szOf d7.words d7.is d7.ih d7.chain 7
meta def wf7 : Array Nat := wfOf d7.words
meta def wn7 : Array Nat := wnOf d7.words

end CertificateChecks.KernelCo2Eleven

#kmisc_packarrs CertificateChecks.KernelCo2Eleven.WV7 CertificateChecks.KernelCo2Eleven.wv7 12
#kmisc_packarrs CertificateChecks.KernelCo2Eleven.WVI7 CertificateChecks.KernelCo2Eleven.wvi7 12
#kmisc_packarrs CertificateChecks.KernelCo2Eleven.R7 CertificateChecks.KernelCo2Eleven.rec7 12
#kss_list CertificateChecks.KernelCo2Eleven.SZ7 CertificateChecks.KernelCo2Eleven.sz7
#kss_list CertificateChecks.KernelCo2Eleven.WF7 CertificateChecks.KernelCo2Eleven.wf7
#kss_list CertificateChecks.KernelCo2Eleven.WN7 CertificateChecks.KernelCo2Eleven.wn7
