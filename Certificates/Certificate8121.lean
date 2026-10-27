module

public import CFSG.RankThree.Native.Co2FiveStructures
import Certificates.Kernel.Misc.Perm.C2Z
import Certificates.Kernel.Misc.Perm.C2K
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Certificate3115
import Certificates.Certificate3117
public import CFSG.Certificates.InvariantMerge
public import CFSG.Sporadic.Co2Cert.Order
import CFSG.Certificates.Kernel.Misc.ArrEnumSound
import CFSG.Certificates.Kernel.Spor.RawOrbGrp
import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore
import Certificates.Kernel.Misc.Perm.CertBind

public section

namespace Certificates

open CertificateChecks

theorem certificate8121 : CFSG.RankThree.Native.Co2FiveStructures :=
  have : Fact CFSG.RankThree.Native.Co2FiveLit.Co2FiveLitChecks := ⟨KernelMisc.Co2K.litChecks⟩
  CFSG.RankThree.Native.Co2FiveLit.co2FiveStructures_of_checks

end Certificates
