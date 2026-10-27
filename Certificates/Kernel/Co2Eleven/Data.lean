module

public import CFSG.HardMathSupport.Dickson.BMRows.Co2ElevenInputs
public meta import CFSG.HardMathSupport.Dickson.BMRows.Co2ElevenInputs
public meta import Certificates.Kernel.Co2Eleven.DataGen
meta import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Kernel.SporSch.Mathieu.Gen
public import Certificates.Kernel.Co2Eleven.DataGen
public import Mathlib
import Certificates.Kernel.Misc.Perm.HexCmd
import Certificates.Kernel.SporSch.Mathieu.Gen

public section

namespace CertificateChecks.KernelCo2Eleven

open CFSG.HardMathSupport.Dickson.BMRows.Co2ElevenNative

meta def d11 := co2ElevenData
meta def wv11 : Array (Array Nat) := wvOf d11.words
meta def wvi11 : Array (Array Nat) := wviOf d11.words
meta def rec11 : Array (Array Nat) := recOf d11.words d11.is d11.ih d11.chain 7
meta def sz11 : Array Nat := szOf d11.words d11.is d11.ih d11.chain 7
meta def wf11 : Array Nat := wfOf d11.words
meta def wn11 : Array Nat := wnOf d11.words

end CertificateChecks.KernelCo2Eleven

#kmisc_packarrs CertificateChecks.KernelCo2Eleven.WV CertificateChecks.KernelCo2Eleven.wv11 12
#kmisc_packarrs CertificateChecks.KernelCo2Eleven.WVI CertificateChecks.KernelCo2Eleven.wvi11 12
#kmisc_packarrs CertificateChecks.KernelCo2Eleven.R CertificateChecks.KernelCo2Eleven.rec11 12
#kss_list CertificateChecks.KernelCo2Eleven.SZ CertificateChecks.KernelCo2Eleven.sz11
#kss_list CertificateChecks.KernelCo2Eleven.WF CertificateChecks.KernelCo2Eleven.wf11
#kss_list CertificateChecks.KernelCo2Eleven.WN CertificateChecks.KernelCo2Eleven.wn11
