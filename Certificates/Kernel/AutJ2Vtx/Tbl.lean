module

public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.Kernel.Spor.MulHQ
public import CFSG.Quasithin.Recognition.St84.AutJ2VtxInputs
meta import CFSG.Quasithin.Recognition.St84.AutJ2VtxInputs
meta import Certificates.Data.CFSGNative.PSL3Four.Basic
meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutOddCore
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.Sporadic.J2
public import CFSG.Sporadic.SmallOddCore.LocalSpec
public import CFSG.Sporadic.Th.F2Spec
meta import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutOddCore
meta import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
meta import CFSG.Sporadic.J2
meta import CFSG.Sporadic.SmallOddCore.LocalSpec
meta import CFSG.Sporadic.Th.F2Spec

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelAJV

open CFSG.Quasithin.F112R.St84.AutJ2Model
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.PSL3Four.Native

meta def invA (a : Array Nat) : Array Nat := CFSG.Monster.B.Co2.Native.invCand 315 a

meta def tM : Array (Array Nat) := (autJ2Tbls.map natArr).toArray

meta def tiM : Array (Array Nat) := tM.map invA

end CertificateChecks.KernelAJV

#kmisc_packarrs CertificateChecks.KernelAJV.AJT CertificateChecks.KernelAJV.tM 9
#kmisc_packarrs CertificateChecks.KernelAJV.AJI CertificateChecks.KernelAJV.tiM 9

end
