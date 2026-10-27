module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.StatementsNineFifteen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig
public import CFSG.LocalAnalysis.UniquenessCase.UC22S217U3B8Main
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21b
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)

variable {G : Type} [Group G] [Finite G]

theorem conclusion76_of_r76Sig {D : Data G} (h76 : F07.R76Sig D) :
    ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p :=
  fun p hp hsp => h76 p hp (D.sig_prime p hp).2 hsp

end CFSG.LocalAnalysis.UniquenessCase.UC22
