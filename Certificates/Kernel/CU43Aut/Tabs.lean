module

public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Inputs
meta import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Inputs
meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain

public section

namespace CertificateChecks.KernelCU43Aut

open CFSG.EvenSporadicStandard.M24Std.CU43

meta def tabsM : Array (Array Nat) := #[deltaArr, phiArr] ++ reps.toArray

meta def tabsIM : Array (Array Nat) := tabsM.map (CFSG.Monster.B.Co2.Native.invCand 820)

end CertificateChecks.KernelCU43Aut

#kmisc_packarrs CertificateChecks.KernelCU43Aut.CU43T CertificateChecks.KernelCU43Aut.tabsM 10
#kmisc_packarrs CertificateChecks.KernelCU43Aut.CU43TI CertificateChecks.KernelCU43Aut.tabsIM 10

end
