module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3SevenGroups
import Certificates.Kernel.Misc.ON.L37Facts
import Certificates.Kernel.Misc.ON.L37Sym0
import Certificates.Kernel.Misc.ON.L37Sym1
import Certificates.Kernel.Misc.ON.L37Rel0
import Certificates.Kernel.Misc.ON.L37Rel1
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3SevenRels

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelMisc.ON

open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3Seven in
open CFSG.RankThree.Native.ONTriple in
theorem certificate291401 : ∀ j l₁ l₂ : ℕ, j < 2 → l₁ < 4 → l₂ < 4 → l₁ < l₂ →
    ∀ m₁ m₂ : ℕ, m₁ < 3 → m₂ < 3 →
      ∃ y : Fin 4 → GM, (∀ w ∈ l37Rels, FreeGroup.lift y (FreeGroup.mk w) = 1) ∧
        Subgroup.closure (Set.range y) = Subgroup.closure (Set.range (pairY j l₁ m₁ l₂ m₂)) :=
  fun j l₁ l₂ hj h₁ h₂ hl m₁ m₂ hm₁ hm₂ => L37.exists_rels_pairK l37Sym0 l37Sym1 (fun j hj => by
      interval_cases j
      · exact l37Rel0
      · exact l37Rel1) j l₁ l₂ hj h₁ h₂ hl m₁ m₂ hm₁ hm₂

end Certificates
