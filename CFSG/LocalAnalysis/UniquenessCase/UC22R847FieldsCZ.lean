module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R847Fields
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsRootModule
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.SigmaCentZ
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ContextFacts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem Ctx23L.normalizer_zpowers_le_M_of_r847ThinCZ {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (h1930 : H1930 D) (h4 : S23_4 D Ch) (h : R847ThinCZ D)
    {K : Subgroup G} (hK : K ∈ calC D.M) (hthin : F08.Thin8 K)
    {a : G} (haK : a ∈ K) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (har : orderOf a = r) :
    normalizer (zpowers a : Set G) ≤ D.M := by
  have hcard : Nat.card (zpowers a) = r := by rw [Nat.card_zpowers, har]
  refine h K hK hthin (zpowers a) (zpowers_le.mpr haK) (by rw [hcard]; exact hr)
    (by rw [hcard]; exact hr2) ?_
  intro hbot
  have hKCZ : K ≤ centralizer (D.Z : Set G) :=
    le_centralizer_Z_of_perfect D Ch h4 h1930 c (CFSG.Open.IsSubnormal.le hK.1) hK.2.1
  have hle : D.Z ≤ pCoreOf 2 D.M ⊓ centralizer (zpowers a : Set G) :=
    le_inf (c.Z_le_pCoreOf_M h4 h1930)
      (le_centralizer_iff.mpr (zpowers_le.mpr (hKCZ haK)))
  rw [hbot] at hle
  exact uc22main1_Z_ne_bot D (le_bot_iff.mp hle)

end CFSG.LocalAnalysis.UniquenessCase.UC22
