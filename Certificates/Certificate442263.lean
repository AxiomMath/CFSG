module

public import Certificates.Data.GH23Data
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutGH23Clos
import Certificates.Kernel.Misc.Perm.GH23TagFacts

public section

namespace Certificates

open CertificateChecks

open CFSG.OddStandard.SmallF3.HarrisU33.GH23Data CFSG.OddStandard.SmallF3.HarrisU33.Outside in
theorem certificate442263 : ∀ m ∈ members, (m.tag matches .solv _ | .two _) = false →
    IsSolvable ↥(gh23Sub m.gens) ∨ ¬ NoNormalTwo (gh23Sub m.gens) ∨ GH23Concl ↥(gh23Sub m.gens) :=
  fun m hm _ => KernelMisc.GH23Tag.members_spec m hm

end Certificates
