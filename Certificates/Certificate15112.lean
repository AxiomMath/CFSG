module

public import CFSG.Sporadic.SuzRecog.RootTwistChecks
import Certificates.Kernel.Sporadic.OddCore.SuzRKZF
import Certificates.Kernel.Sporadic.OddCore.SuzRTG
import Certificates.Kernel.Sporadic.OddCore.SuzRTH

public section

namespace Certificates

open CertificateChecks.KernelSpor

open CFSG in
theorem certificate15112 : CFSG.Sporadic.SuzRecog.RootTwistCheck.permsOK = true ∧
    CFSG.Sporadic.SuzRecog.RootTwistCheck.membersOK = true ∧
    CFSG.Sporadic.SuzRecog.RootTwistCheck.commOK = true ∧
    CFSG.Sporadic.SuzRecog.RootTwistCheck.normOK = true ∧
    CFSG.Sporadic.SuzRecog.RootTwistCheck.sqOK = true ∧
    CFSG.Sporadic.SuzRecog.RootTwistCheck.evenOK = true ∧
    CFSG.Sporadic.SuzRecog.RootTwistCheck.kGenOK = true ∧
    CFSG.Sporadic.SuzRecog.RootTwistCheck.kEnumOK = true ∧
    CFSG.Sporadic.SuzRecog.RootTwistCheck.kCentreOK = true ∧
    CFSG.Sporadic.SuzRecog.RootTwistCheck.classOK = true ∧
    CFSG.Sporadic.SuzRecog.RootTwistCheck.transOK = true ∧
    CFSG.Sporadic.SuzRecog.RootTwistCheck.holOK = true :=
  ⟨SuzRTF.permsOK_true, SuzRTF.membersOK_true, SuzRTF.commOK_true, SuzRTF.normOK_true,
    SuzRTF.sqOK_true, SuzRTF.evenOK_true, SuzRTF.kGenOK_true, SuzRKF.kEnumOK_true,
    SuzRKZF.kCentreOK_true, SuzRTF.classOK_true, SuzRTG.transOK_true, SuzRTH.holOK_true⟩

end Certificates
