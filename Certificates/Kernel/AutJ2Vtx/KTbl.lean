module

public import Certificates.Kernel.AutJ2Vtx.Tbl
meta import CFSG.Quasithin.Recognition.St84.AutJ2VtxInputs
meta import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutOddCore
meta import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
meta import CFSG.Sporadic.J2
meta import CFSG.Sporadic.SmallOddCore.LocalSpec
meta import CFSG.Sporadic.Th.F2Spec

public section

namespace CertificateChecks.KernelAJV

open CFSG.Quasithin.F112R.St84.AutJ2Model CFSG.Sporadic.SmallOddCore.Native

meta def kM : Array (Array Nat) := Array.ofFn (n := 64) fun i => natArr (κRT (q1mOfCode i.val))

end CertificateChecks.KernelAJV

#kmisc_packarrs CertificateChecks.KernelAJV.AJK CertificateChecks.KernelAJV.kM 9

end
