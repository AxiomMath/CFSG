module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3SevenGroups
import Certificates.Kernel.Misc.ON.L37Facts
import Certificates.Kernel.Misc.ON.L37Sym0
import Certificates.Kernel.Misc.ON.L37Sym1
import Certificates.Kernel.Misc.ON.L37In
import Certificates.Kernel.Misc.ON.L37Top0
import Certificates.Kernel.Misc.ON.L37Top1

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelMisc.ON

open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3Seven in
open CFSG.RankThree.Native.ONTriple in
theorem certificate291403 : ∀ j k l m : ℕ, j < 2 → k < 9 → l < 4 → m < 3 →
    m ≠ rowAt j k l →
      Subgroup.closure (Set.range (lY j k) ∪ {xE j l m 0, xE j l m 1}) = (⊤ : Subgroup GM) :=
  fun j k l m hj hk hl hm hne => L37.closure_topK l37Sym0 l37Sym1 l37In (fun j hj => by
      interval_cases j
      · exact l37Top0
      · exact l37Top1) j k l m hj hk hl hm hne

end Certificates
