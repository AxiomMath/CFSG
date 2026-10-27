module

public import Certificates.Data.GH23Data
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutGH23Clos
import Certificates.Kernel.Misc.Perm.GH23LatFacts

public section

namespace Certificates

open CertificateChecks

open CFSG.OddStandard.SmallF3.HarrisU33.GH23Data CFSG.OddStandard.SmallF3.HarrisU33.Outside in
theorem certificate442261 : ∀ m ∈ members, ∀ σ ∈ alternatingGroup (Fin 8), ∃ m' ∈ members,
    gh23Sub m.gens ⊔ Subgroup.zpowers σ = gh23Sub m'.gens :=
  KernelMisc.GH23Lat.gh23Lat_join_closed

end Certificates
