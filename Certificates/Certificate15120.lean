module

public import CFSG.Sporadic.SuzRecog.B0TwistChecks
import Certificates.Kernel.Sporadic.OddCore.SuzTwF
import Certificates.Kernel.Sporadic.OddCore.SuzTwCF

public section

open CFSG

namespace Certificates

open CertificateChecks.KernelSpor

open CFSG in
theorem certificate15120 : CFSG.Sporadic.SuzRecog.B0TwistCheck.twMemOK
    ∧ (CFSG.Sporadic.SuzRecog.B0TwistCheck.twPermsOK = true)
    ∧ (CFSG.Sporadic.SuzRecog.B0TwistCheck.twMembersOK = true)
    ∧ (CFSG.Sporadic.SuzRecog.B0TwistCheck.twCommOK = true)
    ∧ (CFSG.Sporadic.SuzRecog.B0TwistCheck.twTauOK = true)
    ∧ (CFSG.Sporadic.SuzRecog.B0TwistCheck.twRelsOK = true) :=
  ⟨SuzTwF.tw_mem, SuzTwCF.perms, SuzTwCF.members, SuzTwCF.comm, SuzTwCF.tau, SuzTwCF.rels⟩

end Certificates
