module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S218GChain
import CFSG.LocalAnalysis.UniquenessCase.UC22S218Center
import CFSG.LocalAnalysis.UniquenessCase.UC22S218G2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)

variable {G : Type} [Group G] [Finite G]

set_option linter.unusedSectionVars false


theorem uc22s218n_pRank_le_three_G2 (D : Data G) (Ch : Choice2011 G) (hSg : UC6S846.SigmaStd D)
    (h614 : UC6.R6_14 D) (h211 : S21_1 D Ch)
    (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p) (hH : H1930 D)
    (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M) {n : ℕ} (hX : IsG2 (BarInf L) n)
    (hn : ¬ IsPowTwo n) {p : ℕ} (hp : p ∈ D.sig) : CFSG.Open.pRank p D.M ≤ 3 := by
  have hZ : Subgroup.center (Bar2 L) = ⊥ :=
    center_bar2_eq_bot_of_isG2 hL hX (fun h => hn ⟨1, by rw [h]; norm_num⟩)
  refine uc22s218n_pRank_le_three_of_facts D Ch hSg h614 h211 h76 hH c hL (torusFacts218_G2 hX)
    (fun ℓ hℓ hdvd => ?_) hn hp (em _)
  rw [hZ, Subgroup.card_bot] at hdvd
  exact absurd hdvd hℓ.not_dvd_one

end CFSG.LocalAnalysis.UniquenessCase.UC22
