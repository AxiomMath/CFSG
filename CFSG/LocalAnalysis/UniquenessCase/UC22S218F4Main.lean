module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S218GChain
import CFSG.LocalAnalysis.UniquenessCase.UC22S218Center
import CFSG.LocalAnalysis.UniquenessCase.UC22S218F4

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)

variable {G : Type} [Group G] [Finite G]

set_option linter.unusedSectionVars false


theorem uc22s218n_pRank_le_three_2F4 (D : Data G) (Ch : Choice2011 G)
    (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D) (h211 : S21_1 D Ch)
    (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p) (hH : H1930 D)
    (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M) {n : ℕ}
    (hX : LieModel (BarInf L) .twistedF4 0 2 n) (hn : ¬ IsPowTwo n) {p : ℕ} (hp : p ∈ D.sig) :
    CFSG.Open.pRank p D.M ≤ 3 := by
  have hZ : Subgroup.center (Bar2 L) = ⊥ := center_bar2_eq_bot_of_is2F4 hL hX
  refine uc22s218n_pRank_le_three_of_facts D Ch hSg h614 h211 h76 hH c hL
    (torusFacts218_2F4 hX) (fun ℓ hℓ hdvd => ?_) hn hp (em _)
  rw [hZ, Subgroup.card_bot] at hdvd
  exact absurd hdvd hℓ.not_dvd_one

end CFSG.LocalAnalysis.UniquenessCase.UC22
