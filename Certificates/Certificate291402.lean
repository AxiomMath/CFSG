module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3SevenGroups
import Certificates.Kernel.Misc.ON.L37Facts
import Certificates.Kernel.Misc.ON.L37Sym0
import Certificates.Kernel.Misc.ON.L37Sym1
import Certificates.Kernel.Misc.ON.L37In

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelMisc.ON

open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3Seven in
open CFSG.RankThree.Native.ONTriple in
theorem certificate291402 : ∀ j k : ℕ, j < 2 → k < 9 → ∀ i < 4,
    xE j (2 + i / 2) (rowAt j k (2 + i / 2)) (i % 2) ∈ Subgroup.closure (Set.range (lY j k)) :=
  fun j k hj hk i hi => L37.mem_closure_inK l37Sym0 l37Sym1 l37In j k hj hk i hi

end Certificates
