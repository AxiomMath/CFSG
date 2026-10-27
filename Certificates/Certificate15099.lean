module

public import CFSG.Sporadic.SuzRecog.ModelGroupsChecks
import Certificates.Kernel.Sporadic.OddCore.SuzMGJ
import Certificates.Kernel.Sporadic.OddCore.SuzMGN
import Certificates.Kernel.Sporadic.OddCore.SuzMGS
import Certificates.Kernel.Sporadic.OddCore.SuzMGK

public section

open CFSG

namespace Certificates

open CertificateChecks.KernelSpor

open CFSG in
theorem certificate15099 : CFSG.Sporadic.SuzRecog.ModelGroupsCheck.permsOK = true ∧
    CFSG.Sporadic.SuzRecog.ModelGroupsCheck.membersOK = true ∧
    CFSG.Sporadic.SuzRecog.ModelGroupsCheck.commOK = true ∧
    CFSG.Sporadic.SuzRecog.ModelGroupsCheck.basicOK = true ∧
    CFSG.Sporadic.SuzRecog.ModelGroupsCheck.normOK = true ∧
    CFSG.Sporadic.SuzRecog.ModelGroupsCheck.pairOK = true ∧
    CFSG.Sporadic.SuzRecog.ModelGroupsCheck.a4OK = true ∧
    CFSG.Sporadic.SuzRecog.ModelGroupsCheck.cos8OK = true ∧
    CFSG.Sporadic.SuzRecog.ModelGroupsCheck.nr0OK = true ∧
    CFSG.Sporadic.SuzRecog.ModelGroupsCheck.csplitOK = true ∧
    CFSG.Sporadic.SuzRecog.ModelGroupsCheck.c1OK = true ∧
    CFSG.Sporadic.SuzRecog.ModelGroupsCheck.j0rhoOK = true :=
  ⟨SuzMGF.perms15099, SuzMGF.members15099, SuzMGF.comm15099, SuzMGF.basic15099,
    SuzMGF.norm15099, SuzMGF.pair15099, SuzMGF.a415099, SuzMGF.cos815099, SuzMGNC.nr015099,
    SuzMGSC.csplit15099, SuzMGKC.c115099, SuzMGJC.j0rho15099⟩

end Certificates
